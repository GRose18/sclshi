import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import { resolve } from 'node:path'
export default defineConfig({
  plugins: [react()],
  server: { port: 5173 },
  build: { rollupOptions: { input: { casino: resolve(__dirname, 'casino.html') } } },
})
