# METAGON JS

Embed beautiful METAGONS into your react application.

## Installation

Install `metagon` with npm

```bash
  npm i metagon
```

Or

```bash
  yarn add metagon
```

## Usage

```javascript
import Metagon from 'metagon'

function App() {
  return <Metagon score={420} seed={0.43231122} />
}
```

View more examples on [Stackblitz](https://stackblitz.com/edit/metagon-js?file=index.tsx).

## Props

| Parameter | Type     | Description                |
| :-------- | :------- | :------------------------- |
| `score` | `number` | **Required**. The ethrank.io score of the user (0-1000+) |
| `seed` | `number` | **Required**. A random number from 0-1 |
| `bgColor` | `string` | A background color to override the one imposed by `score `|
| `infinite` | `boolean` | Keep drawing, even past the draw limit imposed by `score` (default: `false`) |
| `animated` | `boolean` | Animate or render a still image (default: `true`) |


## Credit & License

Developed by Examp. Original copyright to Matei Copot. Per the author's copyright, you are free to use this code for any lawful purpose, however, attribution must be given to the original author, Matei Copot.