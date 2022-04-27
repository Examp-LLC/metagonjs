import sass from 'rollup-plugin-sass'
import jsx from 'rollup-plugin-jsx'
import typescript from 'rollup-plugin-typescript2'
import esModuleInterop from 'rollup-plugin-es-module-interop'
import pkg from './package.json'

export default {
    input: 'metagon.tsx',
    output: [
      {
        file: pkg.main,
        format: 'cjs',
        exports: 'named',
        sourcemap: true,
        strict: false
      }
    ],
    plugins: [
      sass({ insert: true }),
      typescript({  }),
        esModuleInterop(),
      jsx( {factory: 'React.createElement'} )
    ],
    external: ['react', 'react-dom']
  }