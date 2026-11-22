# Lean certifications — Volumen I — Fundamentos

[Español](#español) · [English](#english)

## Español

**Carpeta:** `Vol-1/Lean/` · **Módulos:** 22 · **Declaraciones `theorem`/`lemma`:** 137 · **Ítems cubiertos del inventario V1.3:** 43 (43 con etiqueta).

Estas copias son un **snapshot de certificación** extraído del repositorio compilable [`TIE-Formal`](https://github.com/RALC-TIE-CREATOR/TIE-Formal). El proyecto completo se compila allí con Mathlib; los archivos de esta carpeta conservan sus `import TieFormal.*` originales. No se incluyen `sorry`, `admit` ni `axiom` en los módulos activos.

### Mapa ítem → certificación

| Ítem | Tipo | Título | Módulo | Declaración(es) Lean |
|---|---|---|---|---|
| PT1 | Definición / postulado | PT1: Existencia e Irreductibilidad Ontológica | Primitivos | — (definiciones/estructura) |
| PT2 | Ecuación | PT2: Independencia y Separación Absoluta | F2Analysis | `pt2_no_cross_term` |
| PT4 | Ecuación | PT4: Homogeneidad Universal | F1QuickWins | `pt4_homogeneity`, `pt4_translation_bijective` |
| PT5 | Ecuación | PT5: Cuantización Fundamental | Primitivos | — (definiciones/estructura) |
| PT6 | Ecuación | PT6: Estructura de Fase Universal | Primitivos | — (definiciones/estructura) |
| PT14 | Ecuación | PT14: Principio de Mínima Acción 4D | RotationalChannel | `rotational_channel_dual`, `rotational_channel_half_Bg` |
| PT14 | Ecuación | PT14: Principio de Mínima Acción 4D | TiempoTeoremas | `lt1_dispersion`, `tt9_Phi_bounds`, `pt14_kinetic_prefactor`, `tt22_alpha1` |
| LT1 | Lema + Demostración + Ecuación | LT1: Relación de dispersión del oscilador fundamental | PDI | `Phi_nonneg`, `Phi_le_one`, `energy_bound`, `Phi_lorentz_bounds` |
| LT1 | Lema + Demostración + Ecuación | LT1: Relación de dispersión del oscilador fundamental | TiempoTeoremas | `lt1_dispersion`, `tt9_Phi_bounds` |
| LT2 | Lema + Demostración + Ecuación | LT2: Relación de dispersión covariante en $\mathcal{S}$ curvo | F1QuickWins | — (definiciones/estructura) |
| LT3 | Lema + Demostración + Ecuación | LT3: Tensor de Einstein para la métrica TIE estática | TensorEstatico | `tt8_core`, `tt8_einstein3` |
| TT1 | Teorema + Demostración + Ecuación | TT1: Cota máxima de energía por muestreo | PDI | — (definiciones/estructura) |
| TT2 | Teorema + Demostración + Ecuación | TT2: Función de distorsión cinemática $\Phi(v)$ | PDI | — (definiciones/estructura) |
| TT3 | Teorema + Demostración + Ecuación | TT3: Simultaneidad absoluta | OrdenTemporal | `tt3_simultaneity`, `tt4_deficit_nonneg`, `tt4_clock_no_exceed` |
| TT4 | Teorema + Demostración + Ecuación | TT4: Invarianza del intervalo temporal absoluto | OrdenTemporal | `tt3_simultaneity`, `tt4_deficit_nonneg`, `tt4_clock_no_exceed`, `tt5_transitive` |
| TT5 | Teorema + Demostración + Ecuación | TT5: Causalidad como orden total | OrdenTemporal | `tt3_simultaneity`, `tt4_deficit_nonneg`, `tt5_transitive`, `tt5_causal_subset_temporal` |
| TT5b | Teorema + Demostración + Ecuación | TT5b: Recuperación de la Relatividad Especial como simetría efectiva | TiempoResueltos | — (definiciones/estructura) |
| TT6 | Teorema + Demostración + Ecuación | TT6: Límite continuo y recuperación del cálculo diferencial | F2Analysis | `tt6_difference_quotient` |
| TT7 | Teorema + Demostración + Ecuación | TT7: Ecuaciones de campo de la TIE en vacío | TensorEstatico | `tt8_core` |
| TT8 | Teorema + Demostración | TT8: Unicidad de la solución de vacío esféricamente simétrica | TensorEstatico | `tt8_core`, `tt8_einstein3`, `tt8_equivalence` |
| TT9 | Teorema + Demostración + Ecuación | TT9: Función de distorsión gravitacional $\Phi(r)$ | TiempoTeoremas | `lt1_dispersion`, `tt9_Phi_bounds`, `tt11_Phi_bounds` |
| TT10 | Teorema + Demostración + Ecuación | TT10: Métrica TIE y comparación con la Relatividad General | F1QuickWins | `tt10_schwarzschild_identity` |
| TT11 | Teorema + Demostración + Ecuación | TT11: Función de distorsión general $\Phi(v, r)$ | TiempoTeoremas | `lt1_dispersion`, `tt11_Phi_bounds`, `tt12_spectrum` |
| TT12 | Teorema + Demostración + Ecuación | TT12: Modos colectivos y emergencia del espectro continuo | TiempoResueltos | `tt12_derivation`, `tt5b_lightcone`, `lapse_Phi_bounds` |
| TT12 | Teorema + Demostración + Ecuación | TT12: Modos colectivos y emergencia del espectro continuo | TiempoTeoremas | `lt1_dispersion`, `tt12_spectrum`, `pt14_kinetic_prefactor` |
| TT13 | Teorema + Demostración + Ecuación | TT13: No-go de rotación del contenedor | BacklogCore | `tt13_no_frame_dragging`, `tt13_lt_zero_iff` |
| TT14 | Teorema + Demostración + Ecuación | TT14: Campo de densidad de información \(\rho_I\) | CampoRhoI | `bridge_h0`, `rhoI_coupling_factor`, `OmegaLT_eq_pos_half_Bg`, `rhoI_tau_factor` |
| TT15 | Teorema + Demostración + Ecuación | TT15: Precesión desde el gradiente de \(\rho_I\) | CampoRhoI | `torque_orthogonal_spin`, `torque_orthogonal_axis`, `scalar_triple_cyclic`, `cross3_antisym` |
| TT16 | Corolario + Demostración + Ecuación | TT16: Precesión de Lense-Thirring (Corolario de TT15) | CampoRhoI | — (definiciones/estructura) |
| TT17 | Teorema + Demostración + Ecuación | TT17: Efecto Sagnac desde \(\mathbf{A}_g\) (cinemático; maquinaria compartida) | F1QuickWins | `co6_sagnac_additive` |
| TT18 | Teorema + Demostración + Ecuación | TT18: Corte del dominio efectivo por discretitud de la red | F1QuickWins | `tt18_domain_nonempty` |
| TT19 | Teorema + Demostración + Ecuación | TT19: Ondas gravitacionales tensoriales en la TIE | TT19Shift | `momentum_constraint_mode`, `vector_velocity_fixed` |
| TT20 | Teorema + Demostración + Ecuación | TT20: Simetría de la sombra en el límite estático | BacklogCore | `tt20_shadow_rotational_symmetry`, `tt20_potential_reflection` |
| TT21 | Teorema + Demostración + Ecuación | TT21: Sombra de agujero negro estático | F1QuickWins | `tt21_sgrA_consistency` |
| TT22 | Lema + Demostración + Ecuación | TT22: Determinación de los parámetros de la acción | TiempoTeoremas | `tt22_alpha1` |
| TT23 | Teorema + Demostración + Ecuación | TT23: Ecuaciones de Friedmann en la TIE (revisión analítica) | CosmologiaTT | `OmegaLambda_pos`, `OmegaLambda_lt_one`, `friedmann_crit_identity`, `wphi_continuity_zero` |
| CO1 | Corolario + Demostración + Ecuación | CO1: Experimento de Hafele-Keating (1971) | F1QuickWins | `co1_distortion_factorization` |
| CO2 | Corolario + Demostración + Ecuación | CO2: GPS y corrección temporal | F1QuickWins | `co2_first_order_product`, `co2_gps_arithmetic` |
| CO3 | Corolario + Demostración + Ecuación | CO3: Redshift gravitacional | F1QuickWins | `co3_redshift_positive` |
| CO5 | Corolario + Demostración | CO5: Precesión de Lense-Thirring desde gradiente de información | F1QuickWins | `co5_gpb_sigma` |
| CO6 | Corolario + Demostración + Ecuación | CO6: Efecto Sagnac desde \(\mathbf{A}_g\) (cinemático) | F1QuickWins | `co6_sagnac_additive` |
| LE1 | Lema + Demostración + Ecuación | LE1: Límite continuo de la red | F2Analysis | `tt6_difference_quotient` |
| LE2 | Lema + Demostración + Ecuación | LE2: Descomposición canónica de la métrica efectiva (definición-lema) | Espacio | `le2_decomposition_unique`, `te_red_diagonal_sum`, `te_red_diagonal_dispersion`, `te_red_vg_consistency` |
| TE1 | Teorema + Demostración + Ecuación | TE1: Planicidad Absoluta de $\mathcal{S}$ | Espacio | `le2_decomposition_unique`, `te_red_diagonal_sum`, `te_red_diagonal_dispersion`, `te1_christoffel_zero`, `te1_riemann_zero` |
| TE2 | Teorema + Demostración + Ecuación | TE2: Carácter Absoluto de la Distancia Espacial | Espacio | `le2_decomposition_unique`, `te_red_diagonal_sum`, `te2_measured_le_absolute` |
| TE4 | Teorema + Demostración | TE4: Ausencia de singularidades intrínsecas en $\mathcal{S}$ | F1QuickWins | `te4_phi_positive` |

### Índice por módulo

| Módulo | Declaraciones | Ítems cubiertos | Capítulo(s) |
|---|---|---|---|
| `BacklogCore` | 13 | 2 | Varios (cierre) |
| `Basic` | 0 | 0 | Base |
| `CampoRhoI` | 10 | 3 | Cap. 1 — TT / Cap. 3 — TM |
| `Coregulator` | 1 | 0 | Base |
| `CosmologiaTT` | 4 | 1 | Cap. 1 — TT / Cap. 9 — TMK |
| `Epochs` | 2 | 0 | Cap. 1 — TT / Cap. 9 — TMK |
| `Espacio` | 7 | 3 | Cap. 2 — TE |
| `F1QuickWins` | 17 | 12 | Varios (cierre) |
| `F2Analysis` | 10 | 3 | Varios (cierre) |
| `Graph21` | 9 | 0 | Cap. 2 — TE / Cap. 4 — TMT |
| `OrdenTemporal` | 5 | 3 | Cap. 1 — TT |
| `PDI` | 7 | 3 | Cap. 1 — TT |
| `Primitivos` | 18 | 3 | Cap. 1 — TT |
| `RhoIField` | 8 | 0 | Cap. 1 — TT / Cap. 3 — TM |
| `RotationalChannel` | 2 | 1 | Cap. 1 — TT |
| `T0Derivation` | 4 | 0 | Cap. 1 — TT |
| `TMKAlgebra` | 3 | 0 | Cap. 1 — TT / Cap. 9 — TMK |
| `TMTCellGraph` | 3 | 0 | Cap. 2 — TE / Cap. 4 — TMT |
| `TT19Shift` | 2 | 1 | Cap. 1 — TT |
| `TensorEstatico` | 3 | 3 | Cap. 1 — TT / Cap. 6 — TMG |
| `TiempoResueltos` | 3 | 2 | Cap. 1 — TT |
| `TiempoTeoremas` | 6 | 6 | Cap. 1 — TT |

<details><summary>Índice completo de declaraciones por módulo</summary>

| Módulo | Declaraciones |
|---|---|
| `BacklogCore` | `tt13_no_frame_dragging`, `tg3_trace_relation`, `tg2_ppn_deviation`, `tg8_power_scaling`, `ta6_trace_perfect_fluid`, `tg1_inverse_expansion`, `tg9_quadratic`, `tt20_shadow_rotational_symmetry`, `tg2_lapse_metric`, `ta6_trace_phase_field`, `tt10_newtonian_limit`, `tt13_lt_zero_iff`, `tt20_potential_reflection` |
| `Basic` | — |
| `CampoRhoI` | `torque_orthogonal_spin`, `torque_orthogonal_axis`, `scalar_triple_cyclic`, `cross3_antisym`, `bridge_h0`, `rhoI_coupling_factor`, `OmegaLT_eq_pos_half_Bg`, `rhoI_tau_factor`, `rhoI_precession_orthogonal`, `hamiltonian_sign` |
| `Coregulator` | `coregulator_identity` |
| `CosmologiaTT` | `OmegaLambda_pos`, `OmegaLambda_lt_one`, `friedmann_crit_identity`, `wphi_continuity_zero` |
| `Epochs` | `t0_positive`, `ages_sum_of_defs` |
| `Espacio` | `le2_decomposition_unique`, `te_red_diagonal_sum`, `te_red_diagonal_dispersion`, `te_red_vg_consistency`, `te2_measured_le_absolute`, `te1_christoffel_zero`, `te1_riemann_zero` |
| `F1QuickWins` | `pt4_homogeneity`, `pt4_translation_bijective`, `co2_first_order_product`, `co2_gps_arithmetic`, `co3_redshift_positive`, `lt2_dispersion_solve`, `tt10_schwarzschild_identity`, `tt21_sgrA_consistency`, `co5_gpb_sigma`, `co6_sagnac_additive`, `co1_distortion_factorization`, `te4_phi_positive`, `tt18_domain_nonempty`, `tt2_phi_factorization`, `lc1_phase_locked`, `lm1_mass_radius_duality`, `tm2_conservation` |
| `F2Analysis` | `tt6_difference_quotient`, `tm4_superposition`, `ta2_stress_symmetry`, `ta1_sqrt_upper`, `ta1_lagrangian_bound`, `ta1_sqrt_lower`, `tm1_free_motion`, `pt2_no_cross_term`, `tg4_conservation`, `ta8_total_conserved` |
| `Graph21` | `node_count`, `nodes_nodup`, `edge_count`, `edge_sum`, `beta1`, `beta1_via_group`, `rootM`, `kink_partition`, `axis_partition` |
| `OrdenTemporal` | `tt3_simultaneity`, `tt4_deficit_nonneg`, `tt4_clock_no_exceed`, `tt5_transitive`, `tt5_causal_subset_temporal` |
| `PDI` | `Phi_nonneg`, `Phi_le_one`, `Phi_bounds`, `Phi_eq_one_iff`, `energy_bound`, `Phi_lorentz_bounds`, `Phi_lorentz_antitone` |
| `Primitivos` | `two_pi_pos`, `sqrt2pi_pos`, `sqrt2pi_ne`, `sq_sqrt2pi`, `T0_ne`, `a0_ne`, `m0_ne`, `c_ne`, `hbar_ne`, `a0_eq_sqrt_lP`, `T0_eq_sqrt_tP`, `G_eq_c`, `lP_sq_a0`, `lP_sq`, `c_mul_tP`, `lP_div_tP`, `hbar_eq_m0`, `E0_eq` |
| `RhoIField` | `crossECLM_apply`, `rpow32`, `rpow52`, `rhoIDipole_grad`, `fderiv_curl_dipole`, `curl_dipole`, `curlE_const_smul`, `curl_Ag` |
| `RotationalChannel` | `rotational_channel_dual`, `rotational_channel_half_Bg` |
| `T0Derivation` | `via2_algebra`, `via2_sqrt`, `via1`, `T0_eq` |
| `TMKAlgebra` | `hubble_value`, `lambda_in_hub`, `hubble_value_autoconsistente` |
| `TMTCellGraph` | `cell_edges_length`, `cell_edges_decomp`, `cell_betti1` |
| `TT19Shift` | `momentum_constraint_mode`, `vector_velocity_fixed` |
| `TensorEstatico` | `tt8_core`, `tt8_einstein3`, `tt8_equivalence` |
| `TiempoResueltos` | `tt12_derivation`, `tt5b_lightcone`, `lapse_Phi_bounds` |
| `TiempoTeoremas` | `lt1_dispersion`, `tt9_Phi_bounds`, `tt11_Phi_bounds`, `tt12_spectrum`, `pt14_kinetic_prefactor`, `tt22_alpha1` |

</details>

### Cómo compilar la base completa

```bash
git clone https://github.com/RALC-TIE-CREATOR/TIE-Formal.git
cd TIE-Formal
lake exe cache get
lake build TieFormal
```

## English

**Folder:** `Vol-1/Lean/` · **Modules:** 22 · **`theorem`/`lemma` declarations:** 137 · **V1.3 inventory items covered:** 43 (43 with label).

These are **certification snapshots** extracted from the buildable [`TIE-Formal`](https://github.com/RALC-TIE-CREATOR/TIE-Formal) repository. The full project builds there with Mathlib; the files here keep their original `import TieFormal.*` lines. Active modules contain no `sorry`, `admit` or `axiom`.

The tables above are language-neutral: `Ítem/Item`, `Tipo/Type`, `Título/Title`, `Módulo/Module`, `Declaración(es)/Declaration(s)`, `Capítulo(s)/Chapter(s)`. The full row-level export is in [`CERTIFICATIONS.csv`](CERTIFICATIONS.csv).

### Citation

Lecona C., R. A. (2026). *TIE — Theory of the Spatial Infrastructure, V1.3* (Vols. I–III). R@LC. CC BY 4.0.
