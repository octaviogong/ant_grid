# ¿El tamaño de la semilla predice cuánto tarda la autopista?

Experimento con 208 reglas caóticas del catálogo (blanco → autopista con transitorio de 1 000 a 2 000 000 pasos).
144 reglas tienen la espera bien medida (≥ 90% de éxitos en 200 tableros 5×5 al azar, hasta 4 millones de pasos).

- `azar.c` / `azar.py`: hormiga generalizada con configuración inicial, detección de autopista, conteo de casillas
  distintas visitadas hasta el inicio, y foto del entorno de la hormiga.
- `experimento.py`: semilla mínima (reducción voraz desde la autopista) y esperas desde tableros al azar → `resultados_semillas.json`.
- `analisis.py`, `analisis2.py`: correlaciones, regresiones y la versión con la estadística del caos.

## Resultados

1. **Búsqueda sin memoria (universal).** Medida en casillas nuevas exploradas, la espera es exponencial:
   coeficiente de variación mediano 1.01 (cuartiles 0.92–1.11); 79% de las reglas entre 0.8 y 1.2.
2. **La semilla importa.** Spearman ρ = +0.54 (p ≈ 2·10⁻¹²) entre casillas de la semilla y log(espera);
   controlando por número de colores y periodo, ρ parcial = +0.31 (p ≈ 10⁻⁴).
3. **Pero no como 2^bits.** La espera crece como (casillas de la semilla)^1.38 ± 0.18 (R² = 0.30), una potencia y no
   una exponencial. Semillas de 4 a 67 casillas (20 a 240 bits si fueran al azar) contra esperas de 7 a 15 bits.
   Con la estadística real del caos tampoco ajusta (pendiente 0.007), y la entropía por casilla del caos no predice nada (ρ = −0.07).

Lectura: el caos no "se saca la lotería" de golpe; parece ensamblar la semilla por partes.
Limitaciones: semillas voraces (no necesariamente mínimas), solo tableros iniciales de 5×5, 200 corridas por regla,
64 reglas excluidas por lentas.

## Robustez (`robustez.py`, `robustez_analisis.py`)

41 reglas (estratificadas por espera, incluida RL), 400 corridas por regla y tres tipos de tablero inicial:
5×5 denso, 9×9 al 30% y 15×15 al 10%.

- **Sin memoria en la cola, medida en casillas**: CV de la cola 1.02–1.05; vida residual media q75/q25 de 1.02 a 1.13.
  **En pasos sí hay memoria**: CV de la cola 1.24–1.35, vida residual 1.36–1.53.
- **La tasa es propia de cada regla**: Spearman 0.995–0.997 entre condiciones; la espera media cambia de 6% a 23%.
- **Ley de la semilla**: Spearman ≈ 0.51 en las tres condiciones (p < 0.001); exponente 1.17–1.33 ± 0.35; R² ≈ 0.24.

Conclusión de lugar: la espera sin memoria va al artículo como observación robusta (sección "Dos regímenes");
la ley de la semilla queda como conjetura preliminar para un trabajo aparte. Ver `../PLAN_ARTICULO.md`.
