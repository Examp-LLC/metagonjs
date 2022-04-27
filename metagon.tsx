// @ts-nocheck
import React, { useEffect, useRef } from 'react';
import PropTypes from 'prop-types';
import styles from './Canvas.module.scss';
import * as seedrandom from 'seedrandom';

const Metagon = (props) => {

  const canvasContainerRef = useRef(null)
  let c;
  let score = props.score;
  let seed = props.seed || Math.random();
  const seed360 = applyRangeToRand(parseFloat(seed.toString()), 360);
  const prng = new seedrandom(seed);
  const scoreRange = 1000;
  const scoreMult = score / scoreRange;
  const startingHue = prng() * 360;

  let w, h, context, opts, tick, lines, dieX, dieY, baseRad, bgColor;

  function init(resize) {

    if (!canvasContainerRef?.current?.clientWidth || c) {
      return;
    }
    c = document.createElement('canvas');
    if (!canvasContainerRef?.current?.children?.length) {
      if (!resize || !props.animated)
        canvasContainerRef.current.appendChild(c);
    }

    w = c.width = canvasContainerRef.current.clientWidth;
    h = c.height = canvasContainerRef.current.clientHeight;
    context = c.getContext('2d');
    opts = {
      len: getLen(scoreMult, seed360), // 40-90
      count: getCount(scoreMult), // 1-5
      baseTime: 40,
      addedTime: 10,
      dieChance: 0.05,
      spawnChance: 1,
      sparkChance: 0.1,
      sparkDist: 30,
      sparkSize: 1,

      color: 'hsl(hue,100%,light%)',
      baseLight: 30,
      addedLight: 10, // [50-10,50+10]
      shadowToTimePropMult: 3,
      baseLightInputMultiplier: 0.5,
      addedLightInputMultiplier: 0.5,

      cx: w / 2,
      cy: h / 2,
      repaintAlpha: 0,
      hueChange: 0.5,
      duration: getDuration(scoreMult),
    },
      tick = 0,
      lines = [],
      dieX = w / 2 / opts.len,
      dieY = h / 2 / opts.len,
      baseRad = (Math.PI * 2) / getPolygonSides(seed360),
      bgColor = props.bgColor || `hsl(${startingHue},100%,${getFillAlpha(scoreMult)}%)`;

    // context.fillStyle = 'transparent';

    context.fillStyle = bgColor;
    context.fillRect(0, 0, w, h);


    loop();


    if (props.animated === false) {
      generateStaticImage();
    }
  

  }

  useEffect(() => {
    init();
  });

  function loop() {
    if (!opts) return;
    if ((tick < opts.duration || props.infinite) && props.animated !== false) {
      window.requestAnimationFrame(loop);
    }
    ++tick;

    context.globalCompositeOperation = 'source-over';
    context.shadowBlur = 0.02;
    context.fillStyle = 'rgba(0,0,0,alp)'.replace('alp', opts.repaintAlpha.toString());
    context.fillRect(0, 0, w, h);
    context.globalCompositeOperation = 'lighter';

    if (lines.length < opts.count && prng() < opts.spawnChance)
      lines.push(new Line());

    lines.map(function (line) {
      line.step();
    });
  }
  function Line() {
    this.reset();
  }
  Line.prototype.reset = function () {
    this.x = 0;
    this.y = 0;
    this.addedX = 0;
    this.addedY = 0;

    this.rad = 0;

    this.lightInputMultiplier =
      opts.baseLightInputMultiplier +
      opts.addedLightInputMultiplier * prng();
    this.color = opts.color.replace('hue', tick * opts.hueChange + startingHue);
    this.cumulativeTime = 0;

    this.beginPhase();
  };
  Line.prototype.beginPhase = function () {
    this.x += this.addedX;
    this.y += this.addedY;

    this.time = 0;
    this.targetTime = (opts.baseTime + opts.addedTime * prng()) | 0;

    this.rad += baseRad * (prng() < 0.5 ? 1 : -1);
    this.addedX = Math.cos(this.rad);
    this.addedY = Math.sin(this.rad);

    if (
      prng() < opts.dieChance ||
      this.x > dieX ||
      this.x < -dieX ||
      this.y > dieY ||
      this.y < -dieY
    )
      this.reset();
  };
  Line.prototype.step = function () {
    ++this.time;
    ++this.cumulativeTime;

    if (this.time >= this.targetTime) this.beginPhase();

    var prop = this.time / this.targetTime,
      wave = Math.sin((prop * Math.PI) / 2),
      x = this.addedX * wave,
      y = this.addedY * wave;

    context.shadowBlur = prop * opts.shadowToTimePropMult;
    context.fillStyle = context.shadowColor = this.color.replace(
      'light',
      opts.baseLight +
      opts.addedLight *
      Math.sin(this.cumulativeTime * this.lightInputMultiplier)
    );
    context.fillRect(
      opts.cx + (this.x + x) * opts.len,
      opts.cy + (this.y + y) * opts.len,
      2,
      2
    );

    if (prng() < opts.sparkChance)
      context.fillRect(
        opts.cx +
        (this.x + x) * opts.len +
        prng() * opts.sparkDist * (prng() < 0.5 ? 1 : -1) -
        opts.sparkSize / 2,
        opts.cy +
        (this.y + y) * opts.len +
        prng() * opts.sparkDist * (prng() < 0.5 ? 1 : -1) -
        opts.sparkSize / 2,
        opts.sparkSize,
        opts.sparkSize
      );
  };

  window.addEventListener('resize', function () {
    init(true);
  });

  function generateStaticImage() {
    tick = 0;
    while (tick < opts.duration) {
      loop();
    }
  }

  init();
  return (
    <div ref={canvasContainerRef} className={styles.wrapper} />
  )
}


Metagon.propTypes = {
  score: PropTypes.number.isRequired,
  seed: PropTypes.number,
  bgColor: PropTypes.string,
  infinite: PropTypes.bool,
  animated: PropTypes.bool,
};


export function getDuration(scoreMult) {
  return Math.abs(1800 + 1400 * scoreMult);
}

export function getLen(scoreMult, seed) {
  let baseLen = 35;
  // triangles are much smaller on the screen than other shapes, embiggen them
  if (getPolygonSides(seed) === 3) {
    baseLen = 50;
  }
  return baseLen + baseLen * scoreMult;
}

export function getCount(scoreMult) {
  const count = scoreMult > .5 ? 7 : 10;
  return Math.abs(count * scoreMult);
}

export function applyRangeToRand(num, max) {
  return Math.floor(num * max);
}

export function getPolygonSides(seed) {
  if (seed > 330) return 8;
  // square
  else if (seed > 280) return 4;
  // hex
  else if (seed > 200) return 6;
  // triangle
  else return 3;
}

export function getFillAlpha(scoreMult) {
  return Math.abs(40 - 40 * scoreMult);
}



export default Metagon;
