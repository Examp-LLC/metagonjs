

function ___$insertStyle(css) {
    if (!css || typeof window === 'undefined') {
        return;
    }
    const style = document.createElement('style');
    style.setAttribute('type', 'text/css');
    style.innerHTML = css;
    document.head.appendChild(style);
    return css;
}

Object.defineProperty(exports, '__esModule', { value: true });

var React = require('react');
var PropTypes = require('prop-types');

function _interopDefault(ex) { return ex && ex.__esModule ? ex.default : ex;}; }

var React__default = /*#__PURE__*/_interopDefaultLegacy(React);
var PropTypes__default = /*#__PURE__*/_interopDefaultLegacy(PropTypes);

var styles = ___$insertStyle(".wrapper {\n  height: 100%;\n  width: 100%;\n}");

// A library of seedable RNGs implemented in Javascript.
//
// Usage:
//
// var seedrandom = require('seedrandom');
// var random = seedrandom(1); // or any seed.
// var x = random();       // 0 <= x < 1.  Every bit is random.
// var x = random.quick(); // 0 <= x < 1.  32 bits of randomness.

// alea, a 53-bit multiply-with-carry generator by Johannes Baagøe.
// Period: ~2^116
// Reported to pass all BigCrush tests.
var alea = require('./lib/alea');

// xor128, a pure xor-shift generator by George Marsaglia.
// Period: 2^128-1.
// Reported to fail: MatrixRank and LinearComp.
var xor128 = require('./lib/xor128');

// xorwow, George Marsaglia's 160-bit xor-shift combined plus weyl.
// Period: 2^192-2^32
// Reported to fail: CollisionOver, SimpPoker, and LinearComp.
var xorwow = require('./lib/xorwow');

// xorshift7, by François Panneton and Pierre L'ecuyer, takes
// a different approach: it adds robustness by allowing more shifts
// than Marsaglia's original three.  It is a 7-shift generator
// with 256 bits, that passes BigCrush with no systmatic failures.
// Period 2^256-1.
// No systematic BigCrush failures reported.
var xorshift7 = require('./lib/xorshift7');

// xor4096, by Richard Brent, is a 4096-bit xor-shift with a
// very long period that also adds a Weyl generator. It also passes
// BigCrush with no systematic failures.  Its long period may
// be useful if you have many generators and need to avoid
// collisions.
// Period: 2^4128-2^32.
// No systematic BigCrush failures reported.
var xor4096 = require('./lib/xor4096');

// Tyche-i, by Samuel Neves and Filipe Araujo, is a bit-shifting random
// number generator derived from ChaCha, a modern stream cipher.
// https://eden.dei.uc.pt/~sneves/pubs/2011-snfa2.pdf
// Period: ~2^127
// No systematic BigCrush failures reported.
var tychei = require('./lib/tychei');

// The original ARC4-based prng included in this library.
// Period: ~2^1600
var sr = require('./seedrandom');

sr.alea = alea;
sr.xor128 = xor128;
sr.xorwow = xorwow;
sr.xorshift7 = xorshift7;
sr.xor4096 = xor4096;
sr.tychei = tychei;

module.exports = sr;

var seedrandom = /*#__PURE__*/Object.freeze({
  __proto__: null
});

// @ts-nocheck
var Metagon = function (props) {
    var canvasContainerRef = React.useRef(null);
    var c;
    var score = props.score;
    var seed = props.seed || Math.random();
    var seed360 = applyRangeToRand(parseFloat(seed.toString()), 360);
    var prng = new seedrandom(seed);
    var scoreRange = 1000;
    var scoreMult = score / scoreRange;
    var startingHue = prng() * 360;
    var w, h, context, opts, tick, lines, dieX, dieY, baseRad, bgColor;
    function init(resize) {
        var _a, _b, _c;
        if (!((_a = canvasContainerRef === null || canvasContainerRef === void 0 ? void 0 : canvasContainerRef.current) === null || _a === void 0 ? void 0 : _a.clientWidth) || c) {
            return;
        }
        c = document.createElement('canvas');
        if (!((_c = (_b = canvasContainerRef === null || canvasContainerRef === void 0 ? void 0 : canvasContainerRef.current) === null || _b === void 0 ? void 0 : _b.children) === null || _c === void 0 ? void 0 : _c.length)) {
            if (!resize || !props.animated)
                canvasContainerRef.current.appendChild(c);
        }
        w = c.width = canvasContainerRef.current.clientWidth;
        h = c.height = canvasContainerRef.current.clientHeight;
        context = c.getContext('2d');
        opts = {
            len: getLen(scoreMult, seed360),
            count: getCount(scoreMult),
            baseTime: 40,
            addedTime: 10,
            dieChance: 0.05,
            spawnChance: 1,
            sparkChance: 0.1,
            sparkDist: 30,
            sparkSize: 1,
            color: 'hsl(hue,100%,light%)',
            baseLight: 30,
            addedLight: 10,
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
            bgColor = props.bgColor || "hsl(".concat(startingHue, ",100%,").concat(getFillAlpha(scoreMult), "%)");
        // context.fillStyle = 'transparent';
        context.fillStyle = bgColor;
        context.fillRect(0, 0, w, h);
        loop();
        if (props.animated === false) {
            generateStaticImage();
        }
    }
    React.useEffect(function () {
        init();
    });
    function loop() {
        if (!opts)
            return;
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
        if (prng() < opts.dieChance ||
            this.x > dieX ||
            this.x < -dieX ||
            this.y > dieY ||
            this.y < -dieY)
            this.reset();
    };
    Line.prototype.step = function () {
        ++this.time;
        ++this.cumulativeTime;
        if (this.time >= this.targetTime)
            this.beginPhase();
        var prop = this.time / this.targetTime, wave = Math.sin((prop * Math.PI) / 2), x = this.addedX * wave, y = this.addedY * wave;
        context.shadowBlur = prop * opts.shadowToTimePropMult;
        context.fillStyle = context.shadowColor = this.color.replace('light', opts.baseLight +
            opts.addedLight *
                Math.sin(this.cumulativeTime * this.lightInputMultiplier));
        context.fillRect(opts.cx + (this.x + x) * opts.len, opts.cy + (this.y + y) * opts.len, 2, 2);
        if (prng() < opts.sparkChance)
            context.fillRect(opts.cx +
                (this.x + x) * opts.len +
                prng() * opts.sparkDist * (prng() < 0.5 ? 1 : -1) -
                opts.sparkSize / 2, opts.cy +
                (this.y + y) * opts.len +
                prng() * opts.sparkDist * (prng() < 0.5 ? 1 : -1) -
                opts.sparkSize / 2, opts.sparkSize, opts.sparkSize);
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
    return (React__default["default"].createElement('div', {ref: canvasContainerRef, className: styles.wrapper}));
};
Metagon.propTypes = {
    score: PropTypes__default["default"].number.isRequired,
    seed: PropTypes__default["default"].number,
    bgColor: PropTypes__default["default"].string,
    infinite: PropTypes__default["default"].bool,
    animated: PropTypes__default["default"].bool,
};
function getDuration(scoreMult) {
    return Math.abs(1800 + 1400 * scoreMult);
}
function getLen(scoreMult, seed) {
    var baseLen = 35;
    // triangles are much smaller on the screen than other shapes, embiggen them
    if (getPolygonSides(seed) === 3) {
        baseLen = 50;
    }
    return baseLen + baseLen * scoreMult;
}
function getCount(scoreMult) {
    var count = scoreMult > .5 ? 7 : 10;
    return Math.abs(count * scoreMult);
}
function applyRangeToRand(num, max) {
    return Math.floor(num * max);
}
function getPolygonSides(seed) {
    if (seed > 330)
        return 8;
    // square
    else if (seed > 280)
        return 4;
    // hex
    else if (seed > 200)
        return 6;
    // triangle
    else
        return 3;
}
function getFillAlpha(scoreMult) {
    return Math.abs(40 - 40 * scoreMult);
}

exports.applyRangeToRand = applyRangeToRand;
exports["default"] = Metagon;
exports.getCount = getCount;
exports.getDuration = getDuration;
exports.getFillAlpha = getFillAlpha;
exports.getLen = getLen;
exports.getPolygonSides = getPolygonSides;
//# sourceMappingURL=index.js.map
