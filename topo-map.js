// Animated topographic contour map in the style of a Swiss hiking map.
// An invisible elevation field (seeded 3D Perlin fbm, drifting through time) is
// contoured with marching squares on every frame. Self-contained: it looks for
// elements with [data-topo-map] holding a <canvas>. Optional attribute on that
// element: data-topo-drift-area (selector; the terrain only drifts while that
// element is on screen).
(function () {
  "use strict";

  const CONFIG = {
    cellSize: 5, // px between elevation samples on normal screens
    maxSamples: 45000, // on big screens cells grow so one frame stays cheap
    // Elevations in metres, in the 2000-3000 m range of the Swiss Alps. Lines are
    // spaced wider than on the 1:50 000 map (20 m) so the background stays calm.
    minorInterval: 40, // m between thin contour lines
    majorInterval: 200, // m between darker, labelled lines
    boldLevels: [2400, 2800], // heavy black lines, chosen inside the usual relief
    base: 2500,
    amplitude: 500,
    frequency: 0.0032, // noise cycles per px
    octaves: 4,
    noiseGain: 1.8, // normalized fbm rarely leaves ±0.5; this stretches it towards ±1
    driftSpeed: 0.000045, // noise time units per ms
    mouseBumpHeight: 190, // m added under the cursor
    mouseBumpRadius: 40, // px, Gaussian sigma
    mouseEasing: 0.07, // fraction of the remaining distance per frame
    labelSpacing: 70, // px, minimum distance between two labels
    labelAnchorSpacing: 190, // px between the anchor points that attract labels
    labelEdgeMargin: 14, // px, keeps labels off the frame
    labelFont: '500 10px "IBM Plex Mono", ui-monospace, monospace',
    summitSize: 5, // px, half the width of the summit triangle
    seed: 1999,
    maxPixelRatio: 2,
    maxFramesPerSecond: 24, // the drift is slow, so more frames only cost CPU
  };

  function mulberry32(seed) {
    let state = seed >>> 0;
    return function () {
      state = (state + 0x6d2b79f5) >>> 0;
      let t = state;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // Ken Perlin's improved noise with a seeded permutation table.
  function createPerlin3D(seed) {
    const random = mulberry32(seed);
    const permutation = Array.from({ length: 256 }, (_, i) => i);
    for (let i = 255; i > 0; i--) {
      const j = Math.floor(random() * (i + 1));
      [permutation[i], permutation[j]] = [permutation[j], permutation[i]];
    }
    const perm = new Uint8Array(512);
    for (let i = 0; i < 512; i++) perm[i] = permutation[i & 255];

    const fade = (t) => t * t * t * (t * (t * 6 - 15) + 10);
    const lerp = (a, b, t) => a + t * (b - a);
    function grad(hash, x, y, z) {
      const h = hash & 15;
      const u = h < 8 ? x : y;
      const v = h < 4 ? y : h === 12 || h === 14 ? x : z;
      return ((h & 1) ? -u : u) + ((h & 2) ? -v : v);
    }

    return function noise(x, y, z) {
      const floorX = Math.floor(x);
      const floorY = Math.floor(y);
      const floorZ = Math.floor(z);
      const X = floorX & 255;
      const Y = floorY & 255;
      const Z = floorZ & 255;
      x -= floorX;
      y -= floorY;
      z -= floorZ;
      const u = fade(x);
      const v = fade(y);
      const w = fade(z);
      const A = perm[X] + Y;
      const AA = perm[A] + Z;
      const AB = perm[A + 1] + Z;
      const B = perm[X + 1] + Y;
      const BA = perm[B] + Z;
      const BB = perm[B + 1] + Z;
      return lerp(
        lerp(
          lerp(grad(perm[AA], x, y, z), grad(perm[BA], x - 1, y, z), u),
          lerp(grad(perm[AB], x, y - 1, z), grad(perm[BB], x - 1, y - 1, z), u),
          v
        ),
        lerp(
          lerp(grad(perm[AA + 1], x, y, z - 1), grad(perm[BA + 1], x - 1, y, z - 1), u),
          lerp(grad(perm[AB + 1], x, y - 1, z - 1), grad(perm[BB + 1], x - 1, y - 1, z - 1), u),
          v
        ),
        w
      );
    };
  }

  function createTopoMap(container) {
    const canvas = container.querySelector("canvas");
    const { topoDriftArea } = container.dataset;
    const driftArea = (topoDriftArea && document.querySelector(topoDriftArea)) || container;
    const context = canvas.getContext("2d");
    const noise = createPerlin3D(CONFIG.seed);
    const reducedMotionQuery = window.matchMedia("(prefers-reduced-motion: reduce)");
    const darkModeQuery = window.matchMedia("(prefers-color-scheme: dark)");

    let width = 0;
    let height = 0;
    let cellSize = CONFIG.cellSize;
    let columns = 0;
    let rows = 0;
    let field = new Float32Array(0);
    let colors = {};

    // Anchor points (in px) that pull labels towards them, rebuilt on resize.
    let labelAnchors = [];

    let time = 0;
    let lastFrameTime = 0;
    let isDrifting = false;
    let frameRequested = false;

    const pointer = { x: 0, y: 0, inside: false };
    const bump = { x: 0, y: 0, strength: 0 };
    const summit = { x: 0, y: 0, elevation: 0 };

    function readColors() {
      const style = getComputedStyle(container);
      const read = (name) => style.getPropertyValue(name).trim();
      colors = {
        background: read("--topo-bg"),
        minor: read("--topo-minor"),
        major: read("--topo-major"),
        bold: read("--topo-bold"),
        label: read("--topo-label"),
        summit: read("--topo-summit"),
      };
    }

    function terrainNoise(x, y) {
      let total = 0;
      let amplitudeSum = 0;
      let octaveAmplitude = 1;
      let octaveFrequency = CONFIG.frequency;
      for (let octave = 0; octave < CONFIG.octaves; octave++) {
        // Offsetting time per octave keeps the octaves from moving in lockstep.
        total += octaveAmplitude * noise(x * octaveFrequency, y * octaveFrequency, time + octave * 17.31);
        amplitudeSum += octaveAmplitude;
        octaveAmplitude *= 0.5;
        octaveFrequency *= 2;
      }
      return (CONFIG.noiseGain * total) / amplitudeSum;
    }

    function elevationAt(x, y) {
      let elevation = CONFIG.base + CONFIG.amplitude * terrainNoise(x, y);
      if (bump.strength > 0.001) {
        const dx = x - bump.x;
        const dy = y - bump.y;
        const sigma = CONFIG.mouseBumpRadius;
        elevation += CONFIG.mouseBumpHeight * bump.strength * Math.exp(-(dx * dx + dy * dy) / (2 * sigma * sigma));
      }
      return elevation;
    }

    function sampleField() {
      summit.elevation = -Infinity;
      for (let row = 0; row < rows; row++) {
        for (let column = 0; column < columns; column++) {
          const x = column * cellSize;
          const y = row * cellSize;
          const elevation = elevationAt(x, y);
          field[row * columns + column] = elevation;
          if (elevation > summit.elevation) {
            summit.elevation = elevation;
            summit.x = x;
            summit.y = y;
          }
        }
      }
    }

    // Marching squares for one cell and one level. Corners: a top-left,
    // b top-right, c bottom-right, d bottom-left.
    const crossings = new Float64Array(8);
    function traceCell(x0, y0, a, b, c, d, level, path, segmentStore) {
      const size = cellSize;
      let count = 0;
      if ((a >= level) !== (b >= level)) {
        crossings[count++] = x0 + ((level - a) / (b - a)) * size;
        crossings[count++] = y0;
      }
      if ((b >= level) !== (c >= level)) {
        crossings[count++] = x0 + size;
        crossings[count++] = y0 + ((level - b) / (c - b)) * size;
      }
      if ((d >= level) !== (c >= level)) {
        crossings[count++] = x0 + ((level - d) / (c - d)) * size;
        crossings[count++] = y0 + size;
      }
      if ((a >= level) !== (d >= level)) {
        crossings[count++] = x0;
        crossings[count++] = y0 + ((level - a) / (d - a)) * size;
      }

      if (count === 4) {
        addSegment(0, 1, level, path, segmentStore);
      } else if (count === 8) {
        // Saddle: crossings are ordered top, right, bottom, left. The cell
        // centre decides whether a and c are joined (cut off b and d) or not.
        const centre = (a + b + c + d) / 4;
        if ((centre >= level) === (a >= level)) {
          addSegment(0, 1, level, path, segmentStore);
          addSegment(2, 3, level, path, segmentStore);
        } else {
          addSegment(0, 3, level, path, segmentStore);
          addSegment(1, 2, level, path, segmentStore);
        }
      }
    }

    function addSegment(firstIndex, secondIndex, level, path, segmentStore) {
      const x1 = crossings[firstIndex * 2];
      const y1 = crossings[firstIndex * 2 + 1];
      const x2 = crossings[secondIndex * 2];
      const y2 = crossings[secondIndex * 2 + 1];
      path.moveTo(x1, y1);
      path.lineTo(x2, y2);
      if (segmentStore) segmentStore.push(x1, y1, x2, y2, level);
    }

    function traceContours() {
      const minorPath = new Path2D();
      const majorPath = new Path2D();
      const boldPath = new Path2D();
      const majorSegments = [];
      const size = cellSize;

      for (let row = 0; row < rows - 1; row++) {
        for (let column = 0; column < columns - 1; column++) {
          const a = field[row * columns + column];
          const b = field[row * columns + column + 1];
          const c = field[(row + 1) * columns + column + 1];
          const d = field[(row + 1) * columns + column];
          const lowest = Math.min(a, b, c, d);
          const highest = Math.max(a, b, c, d);
          const x0 = column * size;
          const y0 = row * size;

          const firstLevel = Math.ceil(lowest / CONFIG.minorInterval) * CONFIG.minorInterval;
          for (let level = firstLevel; level <= highest; level += CONFIG.minorInterval) {
            if (CONFIG.boldLevels.includes(level)) continue;
            if (level % CONFIG.majorInterval === 0) {
              traceCell(x0, y0, a, b, c, d, level, majorPath, majorSegments);
            } else {
              traceCell(x0, y0, a, b, c, d, level, minorPath, null);
            }
          }
          for (const level of CONFIG.boldLevels) {
            if (level >= lowest && level <= highest) {
              // Bold lines on a 100 m level are still labelled like the others.
              const labelStore = level % CONFIG.majorInterval === 0 ? majorSegments : null;
              traceCell(x0, y0, a, b, c, d, level, boldPath, labelStore);
            }
          }
        }
      }
      return { minorPath, majorPath, boldPath, majorSegments };
    }

    function isInsideLabelArea(x, y) {
      const margin = CONFIG.labelEdgeMargin;
      return x >= margin && y >= margin && x <= width - margin && y <= height - margin;
    }

    function drawLabels(majorSegments) {
      const placed = [];
      context.font = CONFIG.labelFont;
      context.textAlign = "center";
      context.textBaseline = "middle";

      for (const [anchorX, anchorY] of labelAnchors) {
        let nearestIndex = -1;
        let nearestDistance = Infinity;
        for (let i = 0; i < majorSegments.length; i += 5) {
          const midX = (majorSegments[i] + majorSegments[i + 2]) / 2;
          const midY = (majorSegments[i + 1] + majorSegments[i + 3]) / 2;
          const distance = (midX - anchorX) ** 2 + (midY - anchorY) ** 2;
          if (distance < nearestDistance) {
            nearestDistance = distance;
            nearestIndex = i;
          }
        }
        if (nearestIndex < 0) continue;

        const x1 = majorSegments[nearestIndex];
        const y1 = majorSegments[nearestIndex + 1];
        const x2 = majorSegments[nearestIndex + 2];
        const y2 = majorSegments[nearestIndex + 3];
        const level = majorSegments[nearestIndex + 4];
        const labelX = (x1 + x2) / 2;
        const labelY = (y1 + y2) / 2;
        if (!isInsideLabelArea(labelX, labelY)) continue;
        const tooClose = placed.some(
          (other) => Math.hypot(other.x - labelX, other.y - labelY) < CONFIG.labelSpacing
        );
        if (tooClose) continue;
        placed.push({ x: labelX, y: labelY });

        let angle = Math.atan2(y2 - y1, x2 - x1);
        if (angle > Math.PI / 2) angle -= Math.PI;
        if (angle < -Math.PI / 2) angle += Math.PI;

        const text = String(level);
        const textWidth = context.measureText(text).width;
        context.save();
        context.translate(labelX, labelY);
        context.rotate(angle);
        context.fillStyle = colors.background;
        context.fillRect(-textWidth / 2 - 3, -6, textWidth + 6, 12);
        context.fillStyle = colors.label;
        context.fillText(text, 0, 0.5);
        context.restore();
      }
    }

    function drawSummit() {
      const size = CONFIG.summitSize;
      context.beginPath();
      context.moveTo(summit.x, summit.y - size);
      context.lineTo(summit.x + size, summit.y + size * 0.75);
      context.lineTo(summit.x - size, summit.y + size * 0.75);
      context.closePath();
      context.fillStyle = colors.summit;
      context.fill();
    }

    function draw() {
      sampleField();
      const { minorPath, majorPath, boldPath, majorSegments } = traceContours();

      context.fillStyle = colors.background;
      context.fillRect(0, 0, width, height);
      context.lineCap = "round";

      context.strokeStyle = colors.minor;
      context.lineWidth = 0.6;
      context.stroke(minorPath);
      context.strokeStyle = colors.major;
      context.lineWidth = 1.1;
      context.stroke(majorPath);
      context.strokeStyle = colors.bold;
      context.lineWidth = 1.5;
      context.stroke(boldPath);

      drawLabels(majorSegments);
      drawSummit();
    }

    function easeBump() {
      const targetStrength = pointer.inside ? 1 : 0;
      if (pointer.inside && bump.strength < 0.01) {
        // Start a new bump under the cursor instead of sliding in from the last spot.
        bump.x = pointer.x;
        bump.y = pointer.y;
      }
      bump.strength += (targetStrength - bump.strength) * CONFIG.mouseEasing;
      bump.x += (pointer.x - bump.x) * 0.25;
      bump.y += (pointer.y - bump.y) * 0.25;

      const strengthSettled = Math.abs(targetStrength - bump.strength) < 0.002;
      if (strengthSettled) bump.strength = targetStrength;
      const positionSettled = !pointer.inside || Math.hypot(pointer.x - bump.x, pointer.y - bump.y) < 0.5;
      return strengthSettled && positionSettled;
    }

    function frame(now) {
      frameRequested = false;
      const minimumFrameInterval = 1000 / CONFIG.maxFramesPerSecond;
      if (lastFrameTime && now - lastFrameTime < minimumFrameInterval - 1) {
        requestFrame();
        return;
      }
      const elapsed = lastFrameTime ? Math.min(now - lastFrameTime, 50) : 16;
      lastFrameTime = now;

      // The terrain drifts only while its drift area is on screen and motion is
      // welcome; otherwise the map holds still and only animates the cursor bump.
      const shouldDrift = isDrifting && !reducedMotionQuery.matches;
      if (shouldDrift) time += elapsed * CONFIG.driftSpeed;
      const bumpSettled = easeBump();
      draw();

      const keepAnimating = shouldDrift || !bumpSettled;
      if (keepAnimating) {
        requestFrame();
      } else {
        lastFrameTime = 0;
      }
    }

    function requestFrame() {
      if (frameRequested || width === 0) return;
      frameRequested = true;
      requestAnimationFrame(frame);
    }

    function resize() {
      const rect = container.getBoundingClientRect();
      width = Math.max(1, Math.round(rect.width));
      height = Math.max(1, Math.round(rect.height));
      const pixelRatio = Math.min(window.devicePixelRatio || 1, CONFIG.maxPixelRatio);
      canvas.width = Math.round(width * pixelRatio);
      canvas.height = Math.round(height * pixelRatio);
      context.setTransform(pixelRatio, 0, 0, pixelRatio, 0, 0);

      cellSize = Math.max(CONFIG.cellSize, Math.sqrt((width * height) / CONFIG.maxSamples));
      columns = Math.ceil(width / cellSize) + 1;
      rows = Math.ceil(height / cellSize) + 1;
      field = new Float32Array(columns * rows);

      // Staggered grid of label anchors so labels spread over the whole map.
      labelAnchors = [];
      const spacing = CONFIG.labelAnchorSpacing;
      for (let rowIndex = 0, y = spacing / 2; y < height; rowIndex++, y += spacing) {
        const rowOffset = rowIndex % 2 === 0 ? spacing / 2 : spacing;
        for (let x = rowOffset; x < width; x += spacing) labelAnchors.push([x, y]);
      }
      requestFrame();
    }

    // The pointer is tracked on the whole window, because page content sits on
    // top of the map and would otherwise swallow the events.
    function updatePointer(event) {
      const rect = canvas.getBoundingClientRect();
      pointer.x = event.clientX - rect.left;
      pointer.y = event.clientY - rect.top;
      pointer.inside = pointer.x >= 0 && pointer.y >= 0 && pointer.x <= width && pointer.y <= height;
      requestFrame();
    }

    function releasePointer() {
      pointer.inside = false;
      requestFrame();
    }

    window.addEventListener("pointermove", updatePointer, { passive: true });
    window.addEventListener("pointerdown", updatePointer, { passive: true });
    window.addEventListener("pointercancel", releasePointer);
    window.addEventListener("pointerup", (event) => {
      if (event.pointerType !== "mouse") releasePointer();
    });
    // A pointerout without a related target means the cursor left the window.
    document.addEventListener("pointerout", (event) => {
      if (!event.relatedTarget) releasePointer();
    });

    darkModeQuery.addEventListener("change", () => {
      readColors();
      requestFrame();
    });
    reducedMotionQuery.addEventListener("change", requestFrame);
    // Labels are measured with the web font, so redraw once it has loaded.
    document.fonts?.ready.then(requestFrame);

    new ResizeObserver(resize).observe(container);
    new IntersectionObserver((entries) => {
      isDrifting = entries[0].isIntersecting;
      requestFrame();
    }).observe(driftArea);

    readColors();
  }

  document.querySelectorAll("[data-topo-map]").forEach(createTopoMap);
})();
