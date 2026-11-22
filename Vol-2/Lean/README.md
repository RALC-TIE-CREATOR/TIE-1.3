# Lean certifications — Volumen II — Materia, Interacciones y Campos

[Español](#español) · [English](#english)

## Español

**Carpeta:** `Vol-2/Lean/` · **Módulos:** 52 · **Declaraciones `theorem`/`lemma`:** 395 · **Ítems cubiertos del inventario V1.3:** 26 (22 con etiqueta).

Estas copias son un **snapshot de certificación** extraído del repositorio compilable [`TIE-Formal`](https://github.com/RALC-TIE-CREATOR/TIE-Formal). El proyecto completo se compila allí con Mathlib; los archivos de esta carpeta conservan sus `import TieFormal.*` originales. No se incluyen `sorry`, `admit` ni `axiom` en los módulos activos.

### Mapa ítem → certificación

| Ítem | Tipo | Título | Módulo | Declaración(es) Lean |
|---|---|---|---|---|
| LC1 | Lema + Demostración + Ecuación | LC1: Acoplamiento de Fases | F1QuickWins | `lc1_phase_locked` |
| LC2 | Lema + Demostración + Ecuación | LC2: Equivalencia de Funciones de Distorsión | F1QuickWins | `co1_distortion_factorization` |
| TM1 | Teorema + Demostración | TM1: Teorema de Movimiento General | F2Analysis | `tm1_free_motion` |
| TM2 | Teorema + Demostración + Ecuación | TM2: Conservación de Propiedades Intrínsecas | F1QuickWins | `tm2_conservation` |
| TM4 | Teorema + Demostración | TM4: Superposición e Interacción de Campos | F2Analysis | `tm4_superposition` |
| LM1 | Lema + Demostración + Ecuación | LM1: Momento Angular Fundamental del Vórtice | F1QuickWins | `lm1_mass_radius_duality` |
| LM2 | Lema + Demostración + Ecuación | LM2: Volúmenes de Configuración de Vórtices Hopf | MateriaLM2 | `lm2_identity`, `lm2_value_interval`, `lm2_vs_mass_ratio` |
| — | Teorema + Ecuación | Por qué el lazo plano es imposible para fermiones | ENTLatticeGen | `exchange_winding_ne_zero` |
| — | Lema + Demostración + Ecuación | El radio mayor de confinamiento | F3Structural | `tmt_radius_relation` |
| — | Ecuación | Mecanismo de espín semientero | ENTLatticeGen | `exchange_winding_ne_zero` |
| — | Teorema + Ecuación | El mecanismo de $\alpha$: la sub-red $\Gamma_{21}$ | AlphaInv | — (definiciones/estructura) |
| — | Teorema + Ecuación | El mecanismo de $\alpha$: la sub-red $\Gamma_{21}$ | TMTGamma21 | — (definiciones/estructura) |
| TA1 | Teorema + Demostración + Ecuación | TA1: Acción de Partícula Puntual en TMA | F2Analysis | `ta1_sqrt_upper`, `ta1_lagrangian_bound`, `ta1_sqrt_lower` |
| TA2 | Teorema + Demostración + Ecuación | TA2: Tensor de Energía-Momento de Partícula Puntual | F2Analysis | `ta2_stress_symmetry` |
| TA4 | Teorema + Demostración + Ecuación | TA4: Acoplamiento Partícula-Campo EM | TMAAlgebra | `magnetic_no_work`, `lorentz_power` |
| TA5 | Teorema + Demostración + Ecuación | TA5: Acción de la Fase Interna en TMA | TA5Shift | `lapse_measure_cancellation`, `quantum_shift_form` |
| TA6 | Teorema + Demostración + Ecuación | TA6: Tensor de Energía-Momento del Campo de Fase | BacklogCore | `ta6_trace_phase_field` |
| TA8 | Demostración + Ecuación | TA8: Tensor de Energía-Momento Total | F2Analysis | `ta8_total_conserved` |
| TG1 | Teorema + Demostración + Ecuación | TG1: Expansión Perturbativa del Campo Gravitacional | BacklogCore | `tg1_inverse_expansion` |
| TG2 | Teorema + Demostración + Ecuación | TG2: Aproximación Post-Newtoniana 1PN | BacklogCore | `tg2_lapse_metric` |
| TG3 | Teorema + Demostración + Ecuación | TG3: Ecuaciones de Campo Gravitacional Exactas | BacklogCore | `tg3_trace_relation` |
| TG4 | Teorema + Demostración + Ecuación | TG4: Identidad variacional, Bianchi y conservación | F2Analysis | `tg4_conservation` |
| TG5 | Teorema + Demostración + Ecuación | TG5: Schwarzschild como solución estática del campo gravitacional | F1QuickWins | `tt10_schwarzschild_identity` |
| TG6 | Teorema + Demostración + Ecuación | TG6: Horizonte como región de campo extremo | F2Analysis | — (definiciones/estructura) |
| TG7 | Teorema + Demostración + Ecuación | TG7: Propagación de Ondas Gravitacionales | GWDispersion | `TT_dispersion` |
| TG8 | Teorema + Demostración + Ecuación | TG8: Potencia radiada por un sistema binario | BacklogCore | `tg8_power_scaling` |
| TG9 | Demostración + Ecuación | TG9: Tensor efectivo de energía-momento gravitacional | BacklogCore | `tg9_quadratic` |

### Índice por módulo

| Módulo | Declaraciones | Ítems cubiertos | Capítulo(s) |
|---|---|---|---|
| `ADMShift` | 2 | 0 | Cap. 6 — TMG |
| `ADMStatic` | 2 | 0 | Cap. 6 — TMG |
| `AlphaInv` | 15 | 1 | Cap. 4 — TMT / Cap. 8 — TME |
| `B4KR` | 2 | 0 | Cap. 4 — TMT (B4) |
| `BacklogCore` | 13 | 6 | Varios (cierre) |
| `CampoRhoI` | 10 | 0 | Cap. 1 — TT / Cap. 3 — TM |
| `Combinatorics` | 7 | 0 | Cap. 4 — TMT |
| `Dispersion` | 5 | 0 | Cap. 6 — TMG |
| `ENTLattice` | 5 | 0 | Cap. 3 — TM / Cap. 7 — TMQ |
| `ENTLatticeGen` | 10 | 2 | Cap. 3 — TM / Cap. 7 — TMQ |
| `ENTP3` | 3 | 0 | Cap. 3 — TM / Cap. 7 — TMQ |
| `ENTPauli` | 3 | 0 | Cap. 3 — TM / Cap. 7 — TMQ |
| `ENTPauliGen` | 6 | 0 | Cap. 3 — TM / Cap. 7 — TMQ |
| `F1QuickWins` | 17 | 5 | Varios (cierre) |
| `F2Analysis` | 10 | 7 | Varios (cierre) |
| `FrameAlgebra` | 6 | 0 | Cap. 6 — TMG |
| `GWDispersion` | 2 | 1 | Cap. 6 — TMG |
| `Graph21` | 9 | 0 | Cap. 2 — TE / Cap. 4 — TMT |
| `MassChains` | 5 | 0 | Cap. 3 — TM / Cap. 4 — TMT |
| `MateriaLM2` | 3 | 1 | Cap. 3 — TM / Cap. 9 — TMK |
| `RhoIField` | 8 | 0 | Cap. 1 — TT / Cap. 3 — TM |
| `TA5Shift` | 2 | 1 | Cap. 5 — TMA |
| `TMAAlgebra` | 2 | 1 | Cap. 5 — TMA |
| `TMGAlgebra` | 1 | 0 | Cap. 6 — TMG |
| `TMTAlgebra` | 2 | 0 | Cap. 5 — TMA |
| `TMTBaryonCatalog` | 10 | 0 | Cap. 4 — TMT |
| `TMTBaryonField` | 4 | 0 | Cap. 4 — TMT |
| `TMTBaryonOrigin` | 5 | 0 | Cap. 4 — TMT |
| `TMTBaryonSpectrum` | 7 | 0 | Cap. 4 — TMT |
| `TMTCellGraph` | 3 | 0 | Cap. 2 — TE / Cap. 4 — TMT |
| `TMTCochains` | 7 | 0 | Cap. 4 — TMT |
| `TMTConfig` | 8 | 0 | Cap. 4 — TMT |
| `TMTFieldPair` | 6 | 0 | Cap. 4 — TMT |
| `TMTFlowPair` | 3 | 0 | Cap. 4 — TMT |
| `TMTGamma21` | 11 | 1 | Cap. 4 — TMT |
| `TMTGraph` | 38 | 0 | Cap. 4 — TMT |
| `TMTMesonStructure` | 5 | 0 | Cap. 4 — TMT |
| `TMTMesons` | 4 | 0 | Cap. 4 — TMT |
| `TMTNeutrinoOrbits` | 5 | 0 | Cap. 4 — TMT |
| `TMTNeutrinoSizes` | 5 | 0 | Cap. 4 — TMT |
| `TMTOctahedral` | 7 | 0 | Cap. 4 — TMT |
| `TMTPendientes` | 5 | 0 | Cap. 4 — TMT |
| `TMTRonda2` | 8 | 0 | Cap. 4 — TMT |
| `TMTRonda2P5` | 48 | 0 | Cap. 4 — TMT |
| `TMTRotations` | 15 | 0 | Cap. 4 — TMT |
| `TMTStability` | 3 | 0 | Cap. 4 — TMT |
| `TMTTStabilizer` | 4 | 0 | Cap. 4 — TMT |
| `TMTTetrahedron` | 6 | 0 | Cap. 4 — TMT |
| `TMTThreeLoops` | 10 | 0 | Cap. 4 — TMT |
| `TMTTicketT01` | 12 | 0 | Cap. 4 — TMT |
| `TMTWinding` | 3 | 0 | Cap. 4 — TMT |
| `TensorEstatico` | 3 | 0 | Cap. 1 — TT / Cap. 6 — TMG |

<details><summary>Índice completo de declaraciones por módulo</summary>

| Módulo | Declaraciones |
|---|---|
| `ADMShift` | `K1_symmetric`, `shift_momentum_constraint` |
| `ADMStatic` | `static_trace_deltaN_zero`, `static_solve_Rij` |
| `AlphaInv` | `alpha_inv_base`, `alpha_inv_base_M`, `alpha_decomposition`, `alpha_factors`, `F1_value`, `F3_value`, `F4_value`, `serie_forma`, `correccion_1loop`, `cota_objetivo_consistente`, `serieRadiativa_acotada`, `serie_cota_pi`, `serie_precision`, `serie_vs_CODATA`, `serieNucleo_acotada` |
| `B4KR` | `kR_half_iff`, `kR_pos` |
| `BacklogCore` | `tt13_no_frame_dragging`, `tg3_trace_relation`, `tg2_ppn_deviation`, `tg8_power_scaling`, `ta6_trace_perfect_fluid`, `tg1_inverse_expansion`, `tg9_quadratic`, `tt20_shadow_rotational_symmetry`, `tg2_lapse_metric`, `ta6_trace_phase_field`, `tt10_newtonian_limit`, `tt13_lt_zero_iff`, `tt20_potential_reflection` |
| `CampoRhoI` | `torque_orthogonal_spin`, `torque_orthogonal_axis`, `scalar_triple_cyclic`, `cross3_antisym`, `bridge_h0`, `rhoI_coupling_factor`, `OmegaLT_eq_pos_half_Bg`, `rhoI_tau_factor`, `rhoI_precession_orthogonal`, `hamiltonian_sign` |
| `Combinatorics` | `plaquette_count`, `plaquettes_nodup`, `plaquette_two_axes`, `axis_distribution`, `kink_antikink_distribution`, `F3_ordered`, `F3_pairs` |
| `Dispersion` | `coef_1_24`, `coef_1_6`, `truncOmega_factor`, `truncOmega_expand`, `truncOmega_correction` |
| `ENTLattice` | `exchange_ticks`, `exchange_swaps`, `rel_path`, `W_single`, `W_double` |
| `ENTLatticeGen` | `angR_one`, `angR_neg_one`, `dAng_antisymm`, `dAng_mod`, `Sraw_telescope`, `Wg_mod`, `exchange_class`, `Wg_backtrack`, `Wg_class_eq`, `exchange_winding_ne_zero` |
| `ENTP3` | `chi_completa`, `chi_trivial`, `puente` |
| `ENTPauli` | `pauli_sq`, `exp_theta_s3_diag`, `exp_pi_s3` |
| `ENTPauliGen` | `exp_theta_s3_cos_sin`, `conjU_spec`, `conjU_det`, `exp_theta_gen`, `exp_pi_gen`, `exp_two_pi_gen` |
| `F1QuickWins` | `pt4_homogeneity`, `pt4_translation_bijective`, `co2_first_order_product`, `co2_gps_arithmetic`, `co3_redshift_positive`, `lt2_dispersion_solve`, `tt10_schwarzschild_identity`, `tt21_sgrA_consistency`, `co5_gpb_sigma`, `co6_sagnac_additive`, `co1_distortion_factorization`, `te4_phi_positive`, `tt18_domain_nonempty`, `tt2_phi_factorization`, `lc1_phase_locked`, `lm1_mass_radius_duality`, `tm2_conservation` |
| `F2Analysis` | `tt6_difference_quotient`, `tm4_superposition`, `ta2_stress_symmetry`, `ta1_sqrt_upper`, `ta1_lagrangian_bound`, `ta1_sqrt_lower`, `tm1_free_motion`, `pt2_no_cross_term`, `tg4_conservation`, `ta8_total_conserved` |
| `FrameAlgebra` | `fin_mk0`, `fin_mk1`, `fin_mk2`, `fin_mk3`, `pderiv_comm'`, `pure_gauge_ricci_zero` |
| `GWDispersion` | `TT_dispersion`, `TT_phase_velocity` |
| `Graph21` | `node_count`, `nodes_nodup`, `edge_count`, `edge_sum`, `beta1`, `beta1_via_group`, `rootM`, `kink_partition`, `axis_partition` |
| `MassChains` | `m4_eq`, `m4_bounds`, `Rtau_gt_aQCD`, `r0_pos`, `kRM_recover` |
| `MateriaLM2` | `lm2_identity`, `lm2_value_interval`, `lm2_vs_mass_ratio` |
| `RhoIField` | `crossECLM_apply`, `rpow32`, `rpow52`, `rhoIDipole_grad`, `fderiv_curl_dipole`, `curl_dipole`, `curlE_const_smul`, `curl_Ag` |
| `TA5Shift` | `lapse_measure_cancellation`, `quantum_shift_form` |
| `TMAAlgebra` | `magnetic_no_work`, `lorentz_power` |
| `TMGAlgebra` | `rho_max_planck` |
| `TMTAlgebra` | `kn_radius`, `poynting_loop` |
| `TMTBaryonCatalog` | `catalogo_invariantes`, `catalogo_relaciones`, `escalera_catalogo`, `p1_kink_antikink`, `p1_linea_cruces`, `p1_L_discrepancia`, `p2_monotonia_2c`, `p2_monotonia_linea`, `p2_monotonia_L`, `p1_cruces_codo` |
| `TMTBaryonField` | `baryon_net_winding_ne_zero`, `baryon_net_winding_odd`, `E_baryon_lower_bound`, `baryon_winding_conserved` |
| `TMTBaryonOrigin` | `E4_six_is_S3`, `E4_six_alt_faces`, `baryon_octet_decuplet`, `S4_order`, `E4_c_scale_hint` |
| `TMTBaryonSpectrum` | `E4_d_over_c`, `E4_b_over_c`, `E4_c_over_base`, `E2_goldstone_massless`, `links_by_baryon`, `links_strictly_increase`, `GMO_octet_within_1pct` |
| `TMTCellGraph` | `cell_edges_length`, `cell_edges_decomp`, `cell_betti1` |
| `TMTCochains` | `gauge_ciclo4`, `gauge_add`, `gauge_refl`, `gauge_symm`, `gauge_trans`, `p2_datos_check`, `p2_inequivalencia` |
| `TMTConfig` | `edges_decomp`, `betti1`, `nodes_decomp`, `O_card`, `O_factor`, `C_values`, `axes_labeled_not_orbit`, `T_examples` |
| `TMTFieldPair` | `pair_raw`, `pair_fixed_by_swap`, `pair_orbits`, `pair_classes_ne_C`, `winding_no_slip`, `E_pair_lower_bound` |
| `TMTFlowPair` | `neutral_pairs_card`, `neutral_classes_mod_neg`, `natural_flow_ne_C` |
| `TMTGamma21` | `Gamma21_nodes`, `Gamma21_edges`, `Gamma21_plaquettes`, `Gamma21_plaq_eq_S4`, `E7_six_is_S3`, `E10_a_over_base`, `E10_integers`, `gamma21_VE`, `gamma21_class_sizes`, `gamma21_separacion`, `gamma21_center_unique_deg12` |
| `TMTGraph` | `cellAdj_symm`, `cellAdj_irrefl`, `cellGraph_edges`, `cellGraph_verts`, `cellGraph_adj_center`, `cellGraph_noLoop`, `cellGraph_symm`, `cellGraph_reachable_center`, `cellGraph_reachable_from_center`, `cellGraph_connected`, `cellGraph_deg_center`, `cellGraph_deg_corner`, `cellGraph_deg8_unique`, `cellGraph_count_deg8`, `cellGraph_count_deg4`, `cellGraph_iso_fixes_center`, `cellEdgeList_types`, `cellGraph_corner_neighbors`, `swapYZFun_inj`, `swapYZFun_surj`, `swapYZEquiv_apply`, `swapYZEquiv_adj`, `flipFun_inj`, `flipFun_surj`, `flipFun_adj`, `flipIso_apply`, `cellGraph_corner0_reaches`, `flipFun_apply_lt`, `cellGraph_corners_transitive`, `pair_edges`, `pair_halves`, `pair_invariants`, `pairEA_invariants`, `pairFA_invariants`, `star_invariants`, `star_rings_touch_only_at_0`, `cube_aut_card`, `n11_invariants` |
| `TMTMesonStructure` | `T_meson_by_mode`, `coupled_structures`, `C_pion_not_from_structure`, `C_kaon_not_from_structure`, `C_meson_values` |
| `TMTMesons` | `kaon_CT`, `pion_CT`, `meson_CT`, `T_structures` |
| `TMTNeutrinoOrbits` | `A4_class_structure`, `neutrino_orbit_ppMM`, `neutrino_orbit_pM00`, `neutrino_doc_ne_A4`, `neutrino_orbit_trivial` |
| `TMTNeutrinoSizes` | `neutrino_configs_total`, `neutrino_orbit_sizes`, `neutrino_size_pM`, `neutrino_size_ppMM`, `E20_phi_hint` |
| `TMTOctahedral` | `orbit_stab_corners`, `orbit_stab_edges`, `orbit_stab_axes`, `orbit_stab_diagonals`, `stab_axis_order`, `sylow2_index_odd`, `axes_orbit_and_stab` |
| `TMTPendientes` | `T11_candidate_structure`, `T11_not_simple_mode`, `meson_T_modes`, `neutrino_A4_summary`, `TMT_pendientes_nota` |
| `TMTRonda2` | `p6_fijos`, `p6_burnside`, `p6_tamanos`, `p6_por_k`, `p7_chi`, `p7_phi`, `selector_deduccion`, `p5_VE` |
| `TMTRonda2P5` | `p5_LS_a0`, `p5_LS_a1`, `p5_LS_a2`, `p5_LS_a3`, `p5_LS_a4`, `p5_LS_a5`, `p5_LS_a6`, `p5_LS_a7`, `p5_LS_a8`, `p5_LS_a9`, `p5_LS_a10`, `p5_LS_a11`, `p5_LS_a12`, `p5_LS_a13`, `p5_LS_a14`, `p5_LS_a15`, `p5_LS_norb`, `p5_LS_eorb`, `p5_LE_a0`, `p5_LE_a1`, `p5_LE_a2`, `p5_LE_a3`, `p5_LE_norb`, `p5_LE_eorb`, `p5_PS_a0`, `p5_PS_a1`, `p5_PS_a2`, `p5_PS_a3`, `p5_PS_a4`, `p5_PS_a5`, `p5_PS_a6`, `p5_PS_a7`, `p5_PS_a8`, `p5_PS_a9`, `p5_PS_a10`, `p5_PS_a11`, `p5_PS_a12`, `p5_PS_a13`, `p5_PS_a14`, `p5_PS_a15`, `p5_PS_norb`, `p5_PS_eorb`, `p5_PE_a0`, `p5_PE_a1`, `p5_PE_a2`, `p5_PE_a3`, `p5_PE_norb`, `p5_PE_eorb` |
| `TMTRotations` | `O_card_rot`, `Oset_one`, `Oset_mul`, `Oset_inv`, `inversion_not_rot`, `orbit_vertex`, `stab_vertex`, `orbit_edge`, `stab_edge`, `orbit_axis`, `stab_axis`, `orbit_diag`, `stab_diag`, `s4_card`, `diag_faithful` |
| `TMTStability` | `Ecycle_w1_n4`, `Ecycle_w0`, `C_min_counts` |
| `TMTTStabilizer` | `kk_pairings_count`, `kk_stab_order`, `kk_orbit_stab`, `kk_stab_is_sylow2` |
| `TMTTetrahedron` | `tetra_VEF`, `tetra_S4`, `tetra_A4`, `tetra_S3`, `tetra_baryon_integers`, `octahedron_dual` |
| `TMTThreeLoops` | `baryon_raw`, `baryon_orbits`, `baryon_68_ne_56`, `baryon_orbits_ne_CT`, `baryon_max_links`, `burnside_id`, `burnside_transposition`, `burnside_transposition_card`, `burnside_3cycle_card`, `burnside_sum` |
| `TMTTicketT01` | `p1_c_def`, `p1_hbar`, `p1_G`, `p1_hbar_errata`, `p1_G_errata`, `p2`, `p3_F1`, `p3_split`, `p3_F4`, `p3_F3`, `p3_edges_dedup`, `p3_alpha` |
| `TMTWinding` | `windTerm_eq_of_band`, `winding_invariant`, `winding_const_of_no_slip` |
| `TensorEstatico` | `tt8_core`, `tt8_einstein3`, `tt8_equivalence` |

</details>

### Resultados B1–B6 relacionados con este volumen

| Código | Módulo(s) | Resultado | Destino en el manuscrito |
|---|---|---|---|
| B4 | `B4KR` | `kR` geométrico = 0.6406; `kR = 1/2` excluido (`kR = 1/2 ⇔ s = π(2+r²)`) | Vol. II, cap. 4 — TMT13 |


### Cómo compilar la base completa

```bash
git clone https://github.com/RALC-TIE-CREATOR/TIE-Formal.git
cd TIE-Formal
lake exe cache get
lake build TieFormal
```

## English

**Folder:** `Vol-2/Lean/` · **Modules:** 52 · **`theorem`/`lemma` declarations:** 395 · **V1.3 inventory items covered:** 26 (22 with label).

These are **certification snapshots** extracted from the buildable [`TIE-Formal`](https://github.com/RALC-TIE-CREATOR/TIE-Formal) repository. The full project builds there with Mathlib; the files here keep their original `import TieFormal.*` lines. Active modules contain no `sorry`, `admit` or `axiom`.

The tables above are language-neutral: `Ítem/Item`, `Tipo/Type`, `Título/Title`, `Módulo/Module`, `Declaración(es)/Declaration(s)`, `Capítulo(s)/Chapter(s)`. The full row-level export is in [`CERTIFICATIONS.csv`](CERTIFICATIONS.csv).

### Citation

Lecona C., R. A. (2026). *TIE — Theory of the Spatial Infrastructure, V1.3* (Vols. I–III). R@LC. CC BY 4.0.
