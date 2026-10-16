# Dinfty reference index

Every top-level declaration and every section of `Release/Dinfty/*.lean` carries a single-line label

```
-- [D-NNNN] name
```

immediately above it. `D-NNNN` is a stable, globally unique citation key; the labels are the only comments in the source. Section labels are marked `§`. Modules are listed in topological (import) order, which is also the order the reference numbers run in — except for labels added after the numbering was fixed (`D-3752` onward), which are appended at the end so that no existing key changes.

| ref | kind | name | module |
|---|---|---|---|
| `D-0001` | structure | `InternalIFS` | `Dinfty.CoreIFS` |
| `D-0002` | structure | `CoreIFS` | `Dinfty.CoreIFS` |
| `D-0003` | class | `TheoremAData` | `Dinfty.CoreIFS` |
| `D-0004` | theorem | `theorem_A` | `Dinfty.CoreIFS` |
| `D-0005` | def | `Fix` | `Dinfty.CoreIFS` |
| `D-0006` | structure | `FixPoints` | `Dinfty.CoreIFS` |
| `D-0007` | class | `FixData` | `Dinfty.CoreIFS` |
| `D-0008` | theorem | `fix_card` | `Dinfty.CoreIFS` |
| `D-0009` | theorem | `equivariant_fixes_fix` | `Dinfty.CoreIFS` |
| `D-0010` | inductive | `InOrbit` | `Dinfty.CoreIFS` |
| `D-0011` | def | `Orbit` | `Dinfty.CoreIFS` |
| `D-0012` | def | `orbitWord` | `Dinfty.CoreIFS` |
| `D-0013` | theorem | `orbit_subset_range_orbitWord` | `Dinfty.CoreIFS` |
| `D-0014` | theorem | `orbit_countable` | `Dinfty.CoreIFS` |
| `D-0015` | theorem | `agree_on_orbit` | `Dinfty.CoreIFS` |
| `D-0016` | theorem | `base_pin` | `Dinfty.CoreIFS` |
| `D-0017` | theorem | `theoremA_unique_of_ingredients` | `Dinfty.CoreIFS` |
| `D-0018` | theorem | `card_axis_obstruction` | `Dinfty.ProdAut` |
| `D-0019` | theorem | `axes_never_match` | `Dinfty.ProdAut` |
| `D-0020` | section | `§ Step 1 — the axes, from the atoms` | `Dinfty.ProdAut` |
| `D-0021` | theorem | `prod_le_iff` | `Dinfty.ProdAut` |
| `D-0022` | theorem | `botB_le_iff` | `Dinfty.ProdAut` |
| `D-0023` | theorem | `axisA_iff` | `Dinfty.ProdAut` |
| `D-0024` | theorem | `botA_le_iff` | `Dinfty.ProdAut` |
| `D-0025` | theorem | `axisB_iff` | `Dinfty.ProdAut` |
| `D-0026` | section | `§ Step 2 — every point is the join of its two shadows` | `Dinfty.ProdAut` |
| `D-0027` | theorem | `isLUB_pair` | `Dinfty.ProdAut` |
| `D-0028` | section | `§ Step 3 — decomposition` | `Dinfty.ProdAut` |
| `D-0029` | theorem | `prod_decomposition_of_axis_preserving` | `Dinfty.ProdAut` |
| `D-0030` | section | `§ Closing the loop: no atom crossing ⟹ axes preserved ⟹ decomposition` | `Dinfty.ProdAut` |
| `D-0031` | theorem | `prod_eq_bot_iff` | `Dinfty.ProdAut` |
| `D-0032` | theorem | `axisA_preserved` | `Dinfty.ProdAut` |
| `D-0033` | theorem | `axisB_preserved` | `Dinfty.ProdAut` |
| `D-0034` | theorem | `prod_decomposition_of_no_crossing` | `Dinfty.ProdAut` |
| `D-0035` | section | `§ Up-sets of the two atom classes` | `Dinfty.ProdAut` |
| `D-0036` | def | `upAatomEquiv` | `Dinfty.ProdAut` |
| `D-0037` | def | `upBatomEquiv` | `Dinfty.ProdAut` |
| `D-0038` | theorem | `card_up_Aatom` | `Dinfty.ProdAut` |
| `D-0039` | theorem | `card_up_Batom` | `Dinfty.ProdAut` |
| `D-0040` | section | `§ The unique atom's up-set is everything but `⊥`` | `Dinfty.ProdAut` |
| `D-0041` | theorem | `le_uniqueAtom_iff` | `Dinfty.ProdAut` |
| `D-0042` | theorem | `card_up_uniqueAtom` | `Dinfty.ProdAut` |
| `D-0043` | section | `§ No crossing, from cardinality` | `Dinfty.ProdAut` |
| `D-0044` | theorem | `up_card_ne` | `Dinfty.ProdAut` |
| `D-0045` | section | `§ Two facts Mathlib does not have: atoms in a product, atoms under an iso` | `Dinfty.ProdAut` |
| `D-0046` | theorem | `prod_ne_bot_iff` | `Dinfty.ProdAut` |
| `D-0047` | theorem | `prod_isAtom_iff` | `Dinfty.ProdAut` |
| `D-0048` | theorem | `orderIso_isAtom` | `Dinfty.ProdAut` |
| `D-0049` | section | `§ Assembly: no crossing, then decomposition` | `Dinfty.ProdAut` |
| `D-0050` | def | `upEquivOfOrderIso` | `Dinfty.ProdAut` |
| `D-0051` | theorem | `card_up_eq` | `Dinfty.ProdAut` |
| `D-0052` | theorem | `no_crossing_B` | `Dinfty.ProdAut` |
| `D-0053` | theorem | `no_crossing_A` | `Dinfty.ProdAut` |
| `D-0054` | theorem | `prod_decomposition_of_card` | `Dinfty.ProdAut` |
| `D-0055` | abbrev | `EndP` | `Dinfty.GluingTowerLibrary` |
| `D-0056` | instance | `inst-Preorder` | `Dinfty.GluingTowerLibrary` |
| `D-0057` | def | `constHom` | `Dinfty.GluingTowerLibrary` |
| `D-0058` | theorem | `constHom_apply` | `Dinfty.GluingTowerLibrary` |
| `D-0059` | def | `meetHom` | `Dinfty.GluingTowerLibrary` |
| `D-0060` | theorem | `meetHom_apply` | `Dinfty.GluingTowerLibrary` |
| `D-0061` | def | `Comp` | `Dinfty.GluingTowerLibrary` |
| `D-0062` | theorem | `bot_comp` | `Dinfty.GluingTowerLibrary` |
| `D-0063` | theorem | `top_comp` | `Dinfty.GluingTowerLibrary` |
| `D-0064` | def | `latticeDecLE` | `Dinfty.GluingTowerLibrary` |
| `D-0065` | def | `JoinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0066` | class | `UniqueAtomCoatom` | `Dinfty.GluingTowerLibrary` |
| `D-0067` | def | `atomOf` | `Dinfty.GluingTowerLibrary` |
| `D-0068` | theorem | `atomOf_ne_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0069` | theorem | `atomOf_le` | `Dinfty.GluingTowerLibrary` |
| `D-0070` | def | `coatomOf` | `Dinfty.GluingTowerLibrary` |
| `D-0071` | theorem | `coatomOf_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0072` | theorem | `coatomOf_le` | `Dinfty.GluingTowerLibrary` |
| `D-0073` | theorem | `atomOf_comparable` | `Dinfty.GluingTowerLibrary` |
| `D-0074` | theorem | `coatomOf_comparable` | `Dinfty.GluingTowerLibrary` |
| `D-0075` | theorem | `inc_atomOf_eq_empty` | `Dinfty.GluingTowerLibrary` |
| `D-0076` | theorem | `inc_coatomOf_eq_empty` | `Dinfty.GluingTowerLibrary` |
| `D-0077` | def | `spikeHom` | `Dinfty.GluingTowerLibrary` |
| `D-0078` | def | `cospikeHom` | `Dinfty.GluingTowerLibrary` |
| `D-0079` | theorem | `spikeHom_apply_top` | `Dinfty.GluingTowerLibrary` |
| `D-0080` | theorem | `spikeHom_apply_of_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0081` | theorem | `cospikeHom_apply_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0082` | theorem | `cospikeHom_apply_of_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0083` | theorem | `spikeHom_atomOf_comp` | `Dinfty.GluingTowerLibrary` |
| `D-0084` | theorem | `cospikeHom_coatomOf_comp` | `Dinfty.GluingTowerLibrary` |
| `D-0085` | theorem | `genreduce` | `Dinfty.GluingTowerLibrary` |
| `D-0086` | def | `latticeOfFiniteSup` | `Dinfty.GluingTowerLibrary` |
| `D-0087` | theorem | `endPBot_apply` | `Dinfty.GluingTowerLibrary` |
| `D-0088` | theorem | `endPTop_apply` | `Dinfty.GluingTowerLibrary` |
| `D-0089` | theorem | `endP_top_eq_constHom_top` | `Dinfty.GluingTowerLibrary` |
| `D-0090` | def | `orderHomEquivSubtype` | `Dinfty.GluingTowerLibrary` |
| `D-0091` | instance | `orderHomDecidableLE` | `Dinfty.GluingTowerLibrary` |
| `D-0092` | instance | `decMonotone` | `Dinfty.GluingTowerLibrary` |
| `D-0093` | instance | `endPFintype` | `Dinfty.GluingTowerLibrary` |
| `D-0094` | instance | `endPDecidableEq` | `Dinfty.GluingTowerLibrary` |
| `D-0095` | instance | `endPBoundedOrder` | `Dinfty.GluingTowerLibrary` |
| `D-0096` | instance | `endPDistribLatticeOfLinearOrder` | `Dinfty.GluingTowerLibrary` |
| `D-0097` | theorem | `endPId_apply` | `Dinfty.GluingTowerLibrary` |
| `D-0098` | theorem | `endPId_ne_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0099` | theorem | `endPId_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0100` | theorem | `endP_bot_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0101` | theorem | `bot_ne_top_of_nontrivial` | `Dinfty.GluingTowerLibrary` |
| `D-0102` | theorem | `existsUnique_atom_of_least_nonzero` | `Dinfty.GluingTowerLibrary` |
| `D-0103` | theorem | `existsUnique_coatom_of_greatest_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0104` | instance | `endPUniqueAtomCoatom` | `Dinfty.GluingTowerLibrary` |
| `D-0105` | theorem | `coatomOf_endP_eq_cospikeHom` | `Dinfty.GluingTowerLibrary` |
| `D-0106` | structure | `Graph` | `Dinfty.GluingTowerLibrary` |
| `D-0107` | def | `prodGraph` | `Dinfty.GluingTowerLibrary` |
| `D-0108` | def | `Graph.Connected` | `Dinfty.GluingTowerLibrary` |
| `D-0109` | theorem | `connected_no_isolated` | `Dinfty.GluingTowerLibrary` |
| `D-0110` | def | `GraphPrime` | `Dinfty.GluingTowerLibrary` |
| `D-0111` | theorem | `hasse_prime_of_degree_one` | `Dinfty.GluingTowerLibrary` |
| `D-0112` | abbrev | `GlueBase` | `Dinfty.GluingTowerLibrary` |
| `D-0113` | def | `tagA` | `Dinfty.GluingTowerLibrary` |
| `D-0114` | def | `tagB` | `Dinfty.GluingTowerLibrary` |
| `D-0115` | def | `tagC` | `Dinfty.GluingTowerLibrary` |
| `D-0116` | def | `canon` | `Dinfty.GluingTowerLibrary` |
| `D-0117` | theorem | `canon_idem` | `Dinfty.GluingTowerLibrary` |
| `D-0118` | def | `GlueCar` | `Dinfty.GluingTowerLibrary` |
| `D-0119` | instance | `inst-P` | `Dinfty.GluingTowerLibrary` |
| `D-0120` | instance | `inst-P` | `Dinfty.GluingTowerLibrary` |
| `D-0121` | def | `incl` | `Dinfty.GluingTowerLibrary` |
| `D-0122` | theorem | `glueCar_bot_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0123` | theorem | `glueCar_nontrivial` | `Dinfty.GluingTowerLibrary` |
| `D-0124` | def | `rawRule` | `Dinfty.GluingTowerLibrary` |
| `D-0125` | def | `occs` | `Dinfty.GluingTowerLibrary` |
| `D-0126` | theorem | `self_mem_occs` | `Dinfty.GluingTowerLibrary` |
| `D-0127` | def | `leGlue` | `Dinfty.GluingTowerLibrary` |
| `D-0128` | instance | `decRawRule` | `Dinfty.GluingTowerLibrary` |
| `D-0129` | instance | `decLeGlue` | `Dinfty.GluingTowerLibrary` |
| `D-0130` | theorem | `rawRule_trans` | `Dinfty.GluingTowerLibrary` |
| `D-0131` | theorem | `occs_canon_mem` | `Dinfty.GluingTowerLibrary` |
| `D-0132` | theorem | `leGlue_refl` | `Dinfty.GluingTowerLibrary` |
| `D-0133` | instance | `inst-P` | `Dinfty.GluingTowerLibrary` |
| `D-0134` | theorem | `GlueCar.le_def` | `Dinfty.GluingTowerLibrary` |
| `D-0135` | theorem | `glue_antisymm` | `Dinfty.GluingTowerLibrary` |
| `D-0136` | theorem | `glue_trans` | `Dinfty.GluingTowerLibrary` |
| `D-0137` | def | `glueCarPartialOrder` | `Dinfty.GluingTowerLibrary` |
| `D-0138` | abbrev | `skelT` | `Dinfty.GluingTowerLibrary` |
| `D-0139` | abbrev | `skelG1` | `Dinfty.GluingTowerLibrary` |
| `D-0140` | abbrev | `skelG2` | `Dinfty.GluingTowerLibrary` |
| `D-0141` | abbrev | `skelL` | `Dinfty.GluingTowerLibrary` |
| `D-0142` | abbrev | `skelG3` | `Dinfty.GluingTowerLibrary` |
| `D-0143` | abbrev | `skelR` | `Dinfty.GluingTowerLibrary` |
| `D-0144` | abbrev | `iotaA` | `Dinfty.GluingTowerLibrary` |
| `D-0145` | abbrev | `iotaB` | `Dinfty.GluingTowerLibrary` |
| `D-0146` | abbrev | `iotaC` | `Dinfty.GluingTowerLibrary` |
| `D-0147` | theorem | `iotaB_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0148` | theorem | `iotaC_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0149` | theorem | `skel_t_le_g1` | `Dinfty.GluingTowerLibrary` |
| `D-0150` | theorem | `skel_g1_le_g2` | `Dinfty.GluingTowerLibrary` |
| `D-0151` | theorem | `skel_g1_le_l` | `Dinfty.GluingTowerLibrary` |
| `D-0152` | theorem | `skel_l_le_g3` | `Dinfty.GluingTowerLibrary` |
| `D-0153` | theorem | `skel_g3_le_r` | `Dinfty.GluingTowerLibrary` |
| `D-0154` | theorem | `skel_g2_le_g3` | `Dinfty.GluingTowerLibrary` |
| `D-0155` | theorem | `skel_not_g2_le_l` | `Dinfty.GluingTowerLibrary` |
| `D-0156` | theorem | `skel_not_l_le_g2` | `Dinfty.GluingTowerLibrary` |
| `D-0157` | theorem | `skel_t_ne_g1` | `Dinfty.GluingTowerLibrary` |
| `D-0158` | theorem | `skel_g1_ne_g2` | `Dinfty.GluingTowerLibrary` |
| `D-0159` | theorem | `skel_g1_ne_l` | `Dinfty.GluingTowerLibrary` |
| `D-0160` | theorem | `skel_g2_ne_g3` | `Dinfty.GluingTowerLibrary` |
| `D-0161` | theorem | `skel_l_ne_g3` | `Dinfty.GluingTowerLibrary` |
| `D-0162` | theorem | `skel_g3_ne_r` | `Dinfty.GluingTowerLibrary` |
| `D-0163` | theorem | `skelT_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0164` | theorem | `skelG1_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0165` | theorem | `skelG2_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0166` | theorem | `skelL_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0167` | theorem | `skelG3_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0168` | theorem | `skelR_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0169` | theorem | `skel_not_ge_of_le_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0170` | theorem | `skel_not_g3_le_g2` | `Dinfty.GluingTowerLibrary` |
| `D-0171` | theorem | `skel_dsi_copyA_le_g2` | `Dinfty.GluingTowerLibrary` |
| `D-0172` | theorem | `skel_dsi_copyC_g2_le` | `Dinfty.GluingTowerLibrary` |
| `D-0173` | theorem | `skel_dsi_copyA_not_g2_le` | `Dinfty.GluingTowerLibrary` |
| `D-0174` | theorem | `skel_dsi_copyC_not_le_g2` | `Dinfty.GluingTowerLibrary` |
| `D-0175` | theorem | `skel_dsi_copyB_incomp` | `Dinfty.GluingTowerLibrary` |
| `D-0176` | theorem | `occs_inl_mem` | `Dinfty.GluingTowerLibrary` |
| `D-0177` | theorem | `tagA_iso` | `Dinfty.GluingTowerLibrary` |
| `D-0178` | theorem | `occs_iotaB_mem` | `Dinfty.GluingTowerLibrary` |
| `D-0179` | theorem | `tagB_iso` | `Dinfty.GluingTowerLibrary` |
| `D-0180` | theorem | `occs_iotaC_mem` | `Dinfty.GluingTowerLibrary` |
| `D-0181` | theorem | `tagC_iso` | `Dinfty.GluingTowerLibrary` |
| `D-0182` | theorem | `iotaB_generic_eq` | `Dinfty.GluingTowerLibrary` |
| `D-0183` | theorem | `iotaC_generic_eq` | `Dinfty.GluingTowerLibrary` |
| `D-0184` | theorem | `occs_iotaA_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0185` | theorem | `occs_iotaB_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0186` | theorem | `occs_iotaC_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0187` | theorem | `leGlue_iotaA_iotaB_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0188` | theorem | `leGlue_iotaA_iotaC_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0189` | theorem | `leGlue_iotaB_iotaC_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0190` | theorem | `not_leGlue_iotaB_iotaA_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0191` | theorem | `not_leGlue_iotaC_iotaA_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0192` | theorem | `not_leGlue_iotaC_iotaB_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0193` | theorem | `leGlue_iotaA_skelG1` | `Dinfty.GluingTowerLibrary` |
| `D-0194` | theorem | `leGlue_skelG1_iotaB` | `Dinfty.GluingTowerLibrary` |
| `D-0195` | theorem | `leGlue_iotaA_skelG2` | `Dinfty.GluingTowerLibrary` |
| `D-0196` | theorem | `leGlue_skelG2_iotaC` | `Dinfty.GluingTowerLibrary` |
| `D-0197` | theorem | `leGlue_iotaB_skelG3` | `Dinfty.GluingTowerLibrary` |
| `D-0198` | theorem | `leGlue_skelG3_iotaC` | `Dinfty.GluingTowerLibrary` |
| `D-0199` | theorem | `generic_cross_copy_AB_factors` | `Dinfty.GluingTowerLibrary` |
| `D-0200` | theorem | `generic_cross_copy_AC_factors` | `Dinfty.GluingTowerLibrary` |
| `D-0201` | theorem | `generic_cross_copy_BC_factors` | `Dinfty.GluingTowerLibrary` |
| `D-0202` | theorem | `not_leGlue_iotaB_iotaA_of_ne_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0203` | theorem | `not_leGlue_iotaC_iotaA_of_ne_bot_ne_m` | `Dinfty.GluingTowerLibrary` |
| `D-0204` | def | `glueA` | `Dinfty.GluingTowerLibrary` |
| `D-0205` | theorem | `glueA_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0206` | theorem | `glueA_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0207` | theorem | `glueA_lt_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0208` | example | `example-leGlue` | `Dinfty.GluingTowerLibrary` |
| `D-0209` | example | `example-leGlue` | `Dinfty.GluingTowerLibrary` |
| `D-0210` | example | `example-Fin` | `Dinfty.GluingTowerLibrary` |
| `D-0211` | example | `example-Fin` | `Dinfty.GluingTowerLibrary` |
| `D-0212` | example | `example-leGlue` | `Dinfty.GluingTowerLibrary` |
| `D-0213` | example | `example-leGlue` | `Dinfty.GluingTowerLibrary` |
| `D-0214` | example | `example` | `Dinfty.GluingTowerLibrary` |
| `D-0215` | example | `example` | `Dinfty.GluingTowerLibrary` |
| `D-0216` | example | `example` | `Dinfty.GluingTowerLibrary` |
| `D-0217` | example | `example-Fin` | `Dinfty.GluingTowerLibrary` |
| `D-0218` | example | `example-Fin` | `Dinfty.GluingTowerLibrary` |
| `D-0219` | example | `example-Fin` | `Dinfty.GluingTowerLibrary` |
| `D-0220` | def | `glueJoinRaw` | `Dinfty.GluingTowerLibrary` |
| `D-0221` | def | `glueJoin` | `Dinfty.GluingTowerLibrary` |
| `D-0222` | theorem | `rawRule_bot_left` | `Dinfty.GluingTowerLibrary` |
| `D-0223` | theorem | `rawRule_top_right` | `Dinfty.GluingTowerLibrary` |
| `D-0224` | theorem | `mem_occs_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0225` | theorem | `glueJoin_le_left` | `Dinfty.GluingTowerLibrary` |
| `D-0226` | theorem | `glueJoin_le_right` | `Dinfty.GluingTowerLibrary` |
| `D-0227` | theorem | `rawRule_join_le` | `Dinfty.GluingTowerLibrary` |
| `D-0228` | def | `joinTarget` | `Dinfty.GluingTowerLibrary` |
| `D-0229` | theorem | `joinTarget_mem_occs` | `Dinfty.GluingTowerLibrary` |
| `D-0230` | theorem | `rawRule_self_dom` | `Dinfty.GluingTowerLibrary` |
| `D-0231` | theorem | `rawRule_joinTarget` | `Dinfty.GluingTowerLibrary` |
| `D-0232` | theorem | `le_glueJoin` | `Dinfty.GluingTowerLibrary` |
| `D-0233` | theorem | `glue_bot_eq` | `Dinfty.GluingTowerLibrary` |
| `D-0234` | theorem | `glue_top_eq` | `Dinfty.GluingTowerLibrary` |
| `D-0235` | def | `glueSemilatticeSup` | `Dinfty.GluingTowerLibrary` |
| `D-0236` | def | `glueOrderBot` | `Dinfty.GluingTowerLibrary` |
| `D-0237` | def | `glueOrderTop` | `Dinfty.GluingTowerLibrary` |
| `D-0238` | def | `glueLattice` | `Dinfty.GluingTowerLibrary` |
| `D-0239` | def | `glueBoundedOrder` | `Dinfty.GluingTowerLibrary` |
| `D-0240` | def | `glueUniqueAtomCoatom` | `Dinfty.GluingTowerLibrary` |
| `D-0241` | example | `example-card` | `Dinfty.GluingTowerLibrary` |
| `D-0242` | example | `example-GlueCar` | `Dinfty.GluingTowerLibrary` |
| `D-0243` | example | `example-GlueCar` | `Dinfty.GluingTowerLibrary` |
| `D-0244` | example | `example-card` | `Dinfty.GluingTowerLibrary` |
| `D-0245` | example | `example-card` | `Dinfty.GluingTowerLibrary` |
| `D-0246` | example | `example` | `Dinfty.GluingTowerLibrary` |
| `D-0247` | example | `example` | `Dinfty.GluingTowerLibrary` |
| `D-0248` | example | `example-card` | `Dinfty.GluingTowerLibrary` |
| `D-0249` | example | `example-GlueCar` | `Dinfty.GluingTowerLibrary` |
| `D-0250` | example | `example-GlueCar` | `Dinfty.GluingTowerLibrary` |
| `D-0251` | theorem | `finThree_rigid` | `Dinfty.GluingTowerLibrary` |
| `D-0252` | theorem | `finite_lattice_eq_sup_joinIrreds` | `Dinfty.GluingTowerLibrary` |
| `D-0253` | theorem | `eq_of_joinIrred_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0254` | theorem | `orderIso_eq_id_of_fixes_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0255` | theorem | `orderIso_eq_of_joinIrred_eq` | `Dinfty.GluingTowerLibrary` |
| `D-0256` | def | `Covers` | `Dinfty.GluingTowerLibrary` |
| `D-0257` | def | `lowerAtBot` | `Dinfty.GluingTowerLibrary` |
| `D-0258` | def | `raiseAtTop` | `Dinfty.GluingTowerLibrary` |
| `D-0259` | theorem | `lowerAtBot_apply_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0260` | theorem | `lowerAtBot_apply_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0261` | theorem | `raiseAtTop_apply_top` | `Dinfty.GluingTowerLibrary` |
| `D-0262` | theorem | `raiseAtTop_apply_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0263` | theorem | `lowerAtBot_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0264` | theorem | `lowerAtBot_le` | `Dinfty.GluingTowerLibrary` |
| `D-0265` | theorem | `lowerAtBot_lt` | `Dinfty.GluingTowerLibrary` |
| `D-0266` | theorem | `raiseAtTop_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0267` | theorem | `raiseAtTop_le` | `Dinfty.GluingTowerLibrary` |
| `D-0268` | theorem | `raiseAtTop_lt` | `Dinfty.GluingTowerLibrary` |
| `D-0269` | theorem | `covers_lowerAtBot` | `Dinfty.GluingTowerLibrary` |
| `D-0270` | theorem | `covers_raiseAtTop` | `Dinfty.GluingTowerLibrary` |
| `D-0271` | theorem | `gap1_second_cover` | `Dinfty.GluingTowerLibrary` |
| `D-0272` | def | `Graph.Hasse` | `Dinfty.GluingTowerLibrary` |
| `D-0273` | instance | `decidableJoinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0274` | def | `JSub` | `Dinfty.GluingTowerLibrary` |
| `D-0275` | instance | `inst-Fintype` | `Dinfty.GluingTowerLibrary` |
| `D-0276` | instance | `inst-DecidableEq` | `Dinfty.GluingTowerLibrary` |
| `D-0277` | def | `stepMap` | `Dinfty.GluingTowerLibrary` |
| `D-0278` | theorem | `stepMap_apply_of_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0279` | theorem | `stepMap_apply_of_not_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0280` | theorem | `stepMap_apply_self` | `Dinfty.GluingTowerLibrary` |
| `D-0281` | theorem | `covers_prod_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0282` | theorem | `stepMap_join` | `Dinfty.GluingTowerLibrary` |
| `D-0283` | theorem | `exists_mem_eq_of_joinIrred_sup` | `Dinfty.GluingTowerLibrary` |
| `D-0284` | theorem | `endP_finset_sup_apply` | `Dinfty.GluingTowerLibrary` |
| `D-0285` | theorem | `endP_stepMap_sup_eq_self` | `Dinfty.GluingTowerLibrary` |
| `D-0286` | theorem | `joinIrred_endP_iff_exists_stepMap` | `Dinfty.GluingTowerLibrary` |
| `D-0287` | theorem | `stepMap_inj_of_ne_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0288` | theorem | `stepMap_le_stepMap_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0289` | def | `jiWitnessX` | `Dinfty.GluingTowerLibrary` |
| `D-0290` | def | `jiWitnessQ` | `Dinfty.GluingTowerLibrary` |
| `D-0291` | theorem | `jiWitness_spec` | `Dinfty.GluingTowerLibrary` |
| `D-0292` | def | `jiEquiv` | `Dinfty.GluingTowerLibrary` |
| `D-0293` | theorem | `stepMap_ne_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0294` | theorem | `stepMap_lt_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0295` | theorem | `stepMap_ji_covers_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0296` | def | `joinBelow` | `Dinfty.GluingTowerLibrary` |
| `D-0297` | theorem | `le_joinBelow` | `Dinfty.GluingTowerLibrary` |
| `D-0298` | theorem | `joinBelow_le` | `Dinfty.GluingTowerLibrary` |
| `D-0299` | def | `updateAt` | `Dinfty.GluingTowerLibrary` |
| `D-0300` | theorem | `updateAt_apply_self` | `Dinfty.GluingTowerLibrary` |
| `D-0301` | theorem | `updateAt_apply_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0302` | theorem | `updateAt_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0303` | theorem | `updateAt_le` | `Dinfty.GluingTowerLibrary` |
| `D-0304` | theorem | `updateAt_lt` | `Dinfty.GluingTowerLibrary` |
| `D-0305` | theorem | `covers_updateAt` | `Dinfty.GluingTowerLibrary` |
| `D-0306` | theorem | `exists_updateAt_of_covers` | `Dinfty.GluingTowerLibrary` |
| `D-0307` | theorem | `covers_iff_exists_updateAt` | `Dinfty.GluingTowerLibrary` |
| `D-0308` | theorem | `joinBelow_le_self` | `Dinfty.GluingTowerLibrary` |
| `D-0309` | theorem | `exists_covBy_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0310` | theorem | `forced_eq_joinBelow_of_unique_cover` | `Dinfty.GluingTowerLibrary` |
| `D-0311` | def | `meetAbove` | `Dinfty.GluingTowerLibrary` |
| `D-0312` | theorem | `meetAbove_le` | `Dinfty.GluingTowerLibrary` |
| `D-0313` | theorem | `le_meetAbove` | `Dinfty.GluingTowerLibrary` |
| `D-0314` | def | `updateAtUp` | `Dinfty.GluingTowerLibrary` |
| `D-0315` | theorem | `updateAtUp_apply_self` | `Dinfty.GluingTowerLibrary` |
| `D-0316` | theorem | `updateAtUp_apply_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0317` | theorem | `updateAtUp_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0318` | theorem | `updateAtUp_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0319` | theorem | `updateAtUp_gt` | `Dinfty.GluingTowerLibrary` |
| `D-0320` | theorem | `covers_updateAtUp` | `Dinfty.GluingTowerLibrary` |
| `D-0321` | theorem | `exists_updateAtUp_of_covers` | `Dinfty.GluingTowerLibrary` |
| `D-0322` | theorem | `covers_iff_exists_updateAtUp` | `Dinfty.GluingTowerLibrary` |
| `D-0323` | theorem | `self_le_meetAbove` | `Dinfty.GluingTowerLibrary` |
| `D-0324` | theorem | `exists_covBy_le` | `Dinfty.GluingTowerLibrary` |
| `D-0325` | theorem | `forced_eq_meetAbove_of_unique_cover` | `Dinfty.GluingTowerLibrary` |
| `D-0326` | theorem | `fact1_forced_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0327` | theorem | `fact2_forced_top` | `Dinfty.GluingTowerLibrary` |
| `D-0328` | theorem | `comp_of_same_witness` | `Dinfty.GluingTowerLibrary` |
| `D-0329` | theorem | `coatomOf_covers_top` | `Dinfty.GluingTowerLibrary` |
| `D-0330` | theorem | `atomOf_covers_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0331` | theorem | `joinBelow_eq_forced` | `Dinfty.GluingTowerLibrary` |
| `D-0332` | theorem | `meetAbove_eq_forced` | `Dinfty.GluingTowerLibrary` |
| `D-0333` | theorem | `dcnmi_same_general` | `Dinfty.GluingTowerLibrary` |
| `D-0334` | theorem | `meetAbove_eq_of_agree_off` | `Dinfty.GluingTowerLibrary` |
| `D-0335` | theorem | `joinBelow_eq_of_agree_off` | `Dinfty.GluingTowerLibrary` |
| `D-0336` | theorem | `second_upcover_of_ne_witness` | `Dinfty.GluingTowerLibrary` |
| `D-0337` | theorem | `eq_coatomOf_of_covers_top` | `Dinfty.GluingTowerLibrary` |
| `D-0338` | theorem | `eq_atomOf_of_covers_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0339` | theorem | `ac_pin_second_upcover` | `Dinfty.GluingTowerLibrary` |
| `D-0340` | theorem | `sig1break_p0_ne_p1_second_upcover` | `Dinfty.GluingTowerLibrary` |
| `D-0341` | theorem | `reflTransGen_symm_of_symm` | `Dinfty.GluingTowerLibrary` |
| `D-0342` | theorem | `hasse_connects_to_top` | `Dinfty.GluingTowerLibrary` |
| `D-0343` | theorem | `hasse_connected_of_lattice` | `Dinfty.GluingTowerLibrary` |
| `D-0344` | theorem | `hasse_bot_degree_one` | `Dinfty.GluingTowerLibrary` |
| `D-0345` | theorem | `hasse_bot_nonempty` | `Dinfty.GluingTowerLibrary` |
| `D-0346` | theorem | `hasse_P_prime` | `Dinfty.GluingTowerLibrary` |
| `D-0347` | theorem | `card_joinIrred_lt` | `Dinfty.GluingTowerLibrary` |
| `D-0348` | theorem | `jiEquiv_adj_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0349` | theorem | `row_col_rel_iso` | `Dinfty.GluingTowerLibrary` |
| `D-0350` | theorem | `jiEquiv_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0351` | theorem | `joinIrred_atomOf` | `Dinfty.GluingTowerLibrary` |
| `D-0352` | instance | `instOrderBotJI` | `Dinfty.GluingTowerLibrary` |
| `D-0353` | theorem | `isAtomic_of_finite` | `Dinfty.GluingTowerLibrary` |
| `D-0354` | instance | `inst-IsAtomic` | `Dinfty.GluingTowerLibrary` |
| `D-0355` | instance | `inst-IsAtomic` | `Dinfty.GluingTowerLibrary` |
| `D-0356` | theorem | `isAtom_toDual_coatomOf` | `Dinfty.GluingTowerLibrary` |
| `D-0357` | theorem | `toDual_atom_unique` | `Dinfty.GluingTowerLibrary` |
| `D-0358` | def | `jiOrderIso` | `Dinfty.GluingTowerLibrary` |
| `D-0359` | theorem | `jh_free` | `Dinfty.GluingTowerLibrary` |
| `D-0360` | theorem | `jh_product_order_level_full` | `Dinfty.GluingTowerLibrary` |
| `D-0361` | theorem | `stepMap_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0362` | theorem | `stepMap_finset_sup` | `Dinfty.GluingTowerLibrary` |
| `D-0363` | theorem | `orderIso_finset_sup` | `Dinfty.GluingTowerLibrary` |
| `D-0364` | def | `tauHat` | `Dinfty.GluingTowerLibrary` |
| `D-0365` | theorem | `tauHat_monotone` | `Dinfty.GluingTowerLibrary` |
| `D-0366` | theorem | `phi_hat_vertical_general` | `Dinfty.GluingTowerLibrary` |
| `D-0367` | theorem | `phi_hat_closed_form` | `Dinfty.GluingTowerLibrary` |
| `D-0368` | theorem | `tauHat_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0369` | theorem | `tauHat_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0370` | def | `HasUniqueDownCover` | `Dinfty.GluingTowerLibrary` |
| `D-0371` | def | `HasUniqueUpCover` | `Dinfty.GluingTowerLibrary` |
| `D-0372` | theorem | `not_hasUniqueUpCover_of_second` | `Dinfty.GluingTowerLibrary` |
| `D-0373` | theorem | `not_hasUniqueDownCover_of_second` | `Dinfty.GluingTowerLibrary` |
| `D-0374` | theorem | `hasUniqueUpCover_of_covers_top` | `Dinfty.GluingTowerLibrary` |
| `D-0375` | theorem | `hasUniqueDownCover_top` | `Dinfty.GluingTowerLibrary` |
| `D-0376` | theorem | `hasUniqueUpCover_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0377` | theorem | `updateAt_witness_eq_of_covers` | `Dinfty.GluingTowerLibrary` |
| `D-0378` | theorem | `updateAtUp_witness_eq_of_covers` | `Dinfty.GluingTowerLibrary` |
| `D-0379` | theorem | `deg11_down_cover_not_uniqueUpCover` | `Dinfty.GluingTowerLibrary` |
| `D-0380` | theorem | `deg11_down_cover_not_covers_top` | `Dinfty.GluingTowerLibrary` |
| `D-0381` | theorem | `covers_glueA_of_covers` | `Dinfty.GluingTowerLibrary` |
| `D-0382` | theorem | `covers_glueA_shape` | `Dinfty.GluingTowerLibrary` |
| `D-0383` | theorem | `hasUniqueDownCover_glueA_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0384` | theorem | `hasUniqueDownCover_glueA_top_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0385` | def | `glueB` | `Dinfty.GluingTowerLibrary` |
| `D-0386` | theorem | `glueB_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0387` | def | `glueL` | `Dinfty.GluingTowerLibrary` |
| `D-0388` | theorem | `leGlue_tagA_skelL_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0389` | theorem | `leGlue_tagB_skelL_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0390` | theorem | `not_leGlue_tagC_skelL` | `Dinfty.GluingTowerLibrary` |
| `D-0391` | theorem | `leGlue_tagB_tagB_imp` | `Dinfty.GluingTowerLibrary` |
| `D-0392` | theorem | `not_leGlue_tagB_tagA` | `Dinfty.GluingTowerLibrary` |
| `D-0393` | theorem | `covers_glueB_of_covers` | `Dinfty.GluingTowerLibrary` |
| `D-0394` | theorem | `covers_glueA_m_of_covers_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0395` | theorem | `leGlue_tagA_tagB_of_le` | `Dinfty.GluingTowerLibrary` |
| `D-0396` | theorem | `glueA_lt_glueB_of_le` | `Dinfty.GluingTowerLibrary` |
| `D-0397` | theorem | `glueB_lt_glueB_of_lt` | `Dinfty.GluingTowerLibrary` |
| `D-0398` | theorem | `glueB_lt_skelL_of_lt` | `Dinfty.GluingTowerLibrary` |
| `D-0399` | theorem | `glueA_m_lt_glueL` | `Dinfty.GluingTowerLibrary` |
| `D-0400` | theorem | `covers_glueL_shape` | `Dinfty.GluingTowerLibrary` |
| `D-0401` | theorem | `hasUniqueDownCover_glueL_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0402` | theorem | `leGlue_tagA_tagB_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0403` | theorem | `leGlue_tagB_tagB_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0404` | theorem | `not_leGlue_tagC_tagB` | `Dinfty.GluingTowerLibrary` |
| `D-0405` | theorem | `glueA_m_lt_glueB` | `Dinfty.GluingTowerLibrary` |
| `D-0406` | theorem | `covers_glueB_of_covers_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0407` | theorem | `covers_glueA_m_of_covers_bot_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0408` | theorem | `covers_glueB_shape_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0409` | theorem | `hasUniqueDownCover_glueB_iff_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0410` | theorem | `leGlue_tagA_tagC` | `Dinfty.GluingTowerLibrary` |
| `D-0411` | theorem | `leGlue_tagB_tagC_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0412` | theorem | `leGlue_tagC_tagC_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0413` | theorem | `leGlue_tagC_tagB_top_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0414` | def | `glueC` | `Dinfty.GluingTowerLibrary` |
| `D-0415` | theorem | `glueC_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0416` | theorem | `glueA_top_lt_glueC` | `Dinfty.GluingTowerLibrary` |
| `D-0417` | theorem | `glueB_top_lt_glueC_of_le` | `Dinfty.GluingTowerLibrary` |
| `D-0418` | theorem | `glueC_lt_glueC_of_lt` | `Dinfty.GluingTowerLibrary` |
| `D-0419` | theorem | `glueA_top_lt_glueB_top` | `Dinfty.GluingTowerLibrary` |
| `D-0420` | theorem | `covers_glueA_top_of_covers_bot_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0421` | theorem | `covers_glueB_top_of_covers_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0422` | theorem | `covers_glueC_of_covers_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0423` | theorem | `covers_glueC_shape_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0424` | theorem | `hasUniqueDownCover_glueC_iff_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0425` | theorem | `joinIrred_of_hasUniqueDownCover` | `Dinfty.GluingTowerLibrary` |
| `D-0426` | theorem | `hasUniqueDownCover_of_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0427` | theorem | `hasUniqueDownCover_iff_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0428` | theorem | `joinIrred_glueA_of_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0429` | theorem | `glueA_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0430` | theorem | `joinIrred_glueB_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0431` | theorem | `joinIrred_glueC_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0432` | theorem | `joinBelow_constHom_eq` | `Dinfty.GluingTowerLibrary` |
| `D-0433` | theorem | `covers_constHom_iff_lowerAtBot` | `Dinfty.GluingTowerLibrary` |
| `D-0434` | theorem | `hasUniqueDownCover_constHom_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0435` | theorem | `gap1_down_cover_has_second_up_cover` | `Dinfty.GluingTowerLibrary` |
| `D-0436` | theorem | `covers_id_updateAt_of_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0437` | theorem | `not_hasUniqueDownCover_id_of_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0438` | section | `§ copy embeddings as total maps `P → GlueCar m`` | `Dinfty.GluingTowerLibrary` |
| `D-0439` | def | `glueBt` | `Dinfty.GluingTowerLibrary` |
| `D-0440` | def | `glueCt` | `Dinfty.GluingTowerLibrary` |
| `D-0441` | def | `unA` | `Dinfty.GluingTowerLibrary` |
| `D-0442` | def | `unB` | `Dinfty.GluingTowerLibrary` |
| `D-0443` | def | `unC` | `Dinfty.GluingTowerLibrary` |
| `D-0444` | theorem | `unA_glueA` | `Dinfty.GluingTowerLibrary` |
| `D-0445` | theorem | `unB_glueBt` | `Dinfty.GluingTowerLibrary` |
| `D-0446` | theorem | `unC_glueCt` | `Dinfty.GluingTowerLibrary` |
| `D-0447` | theorem | `glueBt_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0448` | theorem | `glueCt_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0449` | section | `§ canonicity extraction` | `Dinfty.GluingTowerLibrary` |
| `D-0450` | theorem | `canon_inr_inl_ne_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0451` | theorem | `canon_inr_inr_ne` | `Dinfty.GluingTowerLibrary` |
| `D-0452` | theorem | `occs_inr_inl_mem` | `Dinfty.GluingTowerLibrary` |
| `D-0453` | theorem | `occs_inr_inr_mem` | `Dinfty.GluingTowerLibrary` |
| `D-0454` | theorem | `occs_inr_inl_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0455` | section | `§ shape lemmas` | `Dinfty.GluingTowerLibrary` |
| `D-0456` | theorem | `le_tagA_shape` | `Dinfty.GluingTowerLibrary` |
| `D-0457` | theorem | `tagA_top_le_shape` | `Dinfty.GluingTowerLibrary` |
| `D-0458` | theorem | `le_tagB_shape` | `Dinfty.GluingTowerLibrary` |
| `D-0459` | theorem | `tagB_le_shape` | `Dinfty.GluingTowerLibrary` |
| `D-0460` | theorem | `incomp_g2_shape` | `Dinfty.GluingTowerLibrary` |
| `D-0461` | theorem | `tagA_le_tagC` | `Dinfty.GluingTowerLibrary` |
| `D-0462` | theorem | `tagA_le_g3` | `Dinfty.GluingTowerLibrary` |
| `D-0463` | section | `§ two purely `P`-level counting facts` | `Dinfty.GluingTowerLibrary` |
| `D-0464` | theorem | `ncard_down_add_strict_up_lt` | `Dinfty.GluingTowerLibrary` |
| `D-0465` | theorem | `ncard_strict_down_add_up_le` | `Dinfty.GluingTowerLibrary` |
| `D-0466` | section | `§ down-sets / up-sets in `Φ(P)`` | `Dinfty.GluingTowerLibrary` |
| `D-0467` | def | `gDown` | `Dinfty.GluingTowerLibrary` |
| `D-0468` | def | `gUp` | `Dinfty.GluingTowerLibrary` |
| `D-0469` | theorem | `gDown_ncard_map` | `Dinfty.GluingTowerLibrary` |
| `D-0470` | theorem | `gUp_ncard_map` | `Dinfty.GluingTowerLibrary` |
| `D-0471` | theorem | `gDown_glueA` | `Dinfty.GluingTowerLibrary` |
| `D-0472` | theorem | `glueA_inj` | `Dinfty.GluingTowerLibrary` |
| `D-0473` | theorem | `glueCt_inj` | `Dinfty.GluingTowerLibrary` |
| `D-0474` | theorem | `glueBt_inj` | `Dinfty.GluingTowerLibrary` |
| `D-0475` | theorem | `gDown_g2_ncard` | `Dinfty.GluingTowerLibrary` |
| `D-0476` | theorem | `gUp_g2_ncard_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0477` | section | `§ the pinning theorem` | `Dinfty.GluingTowerLibrary` |
| `D-0478` | theorem | `glue_g2_unique` | `Dinfty.GluingTowerLibrary` |
| `D-0479` | theorem | `glue_g2_pinned` | `Dinfty.GluingTowerLibrary` |
| `D-0480` | section | `§ the UP-TRANSFER assembly` | `Dinfty.GluingTowerLibrary` |
| `D-0481` | theorem | `glue_copy_fixed` | `Dinfty.GluingTowerLibrary` |
| `D-0482` | theorem | `glue_rigid_of_incomparable` | `Dinfty.GluingTowerLibrary` |
| `D-0483` | class | `GluingTower` | `Dinfty.GluingTowerLibrary` |
| `D-0484` | class | `GluingTowerUp` | `Dinfty.GluingTowerLibrary` |
| `D-0485` | class | `GluingTowerDown` | `Dinfty.GluingTowerLibrary` |
| `D-0486` | theorem | `connected_of_le_subtype` | `Dinfty.GluingTowerLibrary` |
| `D-0487` | theorem | `connected_of_le_subtype'` | `Dinfty.GluingTowerLibrary` |
| `D-0488` | theorem | `atomOf_hasUniqueDownCover` | `Dinfty.GluingTowerLibrary` |
| `D-0489` | theorem | `hasse_hasUniqueDownCover_glueCar_connected` | `Dinfty.GluingTowerLibrary` |
| `D-0490` | theorem | `connected_of_pointwise_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0491` | theorem | `covers_orderIso` | `Dinfty.GluingTowerLibrary` |
| `D-0492` | theorem | `joinIrred_orderIso` | `Dinfty.GluingTowerLibrary` |
| `D-0493` | theorem | `tauHat_eq_of_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0494` | theorem | `aut_D_k_trivial` | `Dinfty.GluingTowerLibrary` |
| `D-0495` | theorem | `aut_D_infinity_trivial` | `Dinfty.GluingTowerLibrary` |
| `D-0496` | theorem | `constHom_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0497` | theorem | `constHom_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0498` | theorem | `meetHom_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0499` | theorem | `meetHom_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0500` | theorem | `meetHom_top` | `Dinfty.GluingTowerLibrary` |
| `D-0501` | theorem | `meetHom_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0502` | def | `pGen` | `Dinfty.GluingTowerLibrary` |
| `D-0503` | theorem | `pGen_section` | `Dinfty.GluingTowerLibrary` |
| `D-0504` | theorem | `not_leGlue_tagC_tagA` | `Dinfty.GluingTowerLibrary` |
| `D-0505` | theorem | `le_glueA_imp_glueA_shaped` | `Dinfty.GluingTowerLibrary` |
| `D-0506` | theorem | `glueA_sup` | `Dinfty.GluingTowerLibrary` |
| `D-0507` | theorem | `glueA_inf` | `Dinfty.GluingTowerLibrary` |
| `D-0508` | theorem | `glueA_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0509` | theorem | `joinIrred_glueA_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0510` | theorem | `constHom_sup` | `Dinfty.GluingTowerLibrary` |
| `D-0511` | theorem | `constHom_inf` | `Dinfty.GluingTowerLibrary` |
| `D-0512` | theorem | `leGlue_tagA_tagB_top` | `Dinfty.GluingTowerLibrary` |
| `D-0513` | theorem | `ne_bot_of_canon_tagB` | `Dinfty.GluingTowerLibrary` |
| `D-0514` | theorem | `ne_bot_of_canon_tagC` | `Dinfty.GluingTowerLibrary` |
| `D-0515` | theorem | `pGen_deflation` | `Dinfty.GluingTowerLibrary` |
| `D-0516` | theorem | `pGen_monotone` | `Dinfty.GluingTowerLibrary` |
| `D-0517` | theorem | `pGen_top` | `Dinfty.GluingTowerLibrary` |
| `D-0518` | theorem | `directedOn_exists_greatest_of_finite` | `Dinfty.GluingTowerLibrary` |
| `D-0519` | theorem | `monotone_sSup_image_of_finite_directed` | `Dinfty.GluingTowerLibrary` |
| `D-0520` | theorem | `monotone_scottContinuous_of_finite` | `Dinfty.GluingTowerLibrary` |
| `D-0521` | theorem | `monotone_scottContinuous_of_finite_dom` | `Dinfty.GluingTowerLibrary` |
| `D-0522` | def | `ScottEndP` | `Dinfty.GluingTowerLibrary` |
| `D-0523` | theorem | `directedOn_image_of_monotone` | `Dinfty.GluingTowerLibrary` |
| `D-0524` | abbrev | `GlueBaseGen` | `Dinfty.GluingTowerLibrary` |
| `D-0525` | def | `canonGen` | `Dinfty.GluingTowerLibrary` |
| `D-0526` | theorem | `canonGen_idem` | `Dinfty.GluingTowerLibrary` |
| `D-0527` | def | `GlueCarGen` | `Dinfty.GluingTowerLibrary` |
| `D-0528` | def | `rawRuleGen` | `Dinfty.GluingTowerLibrary` |
| `D-0529` | def | `occsGen` | `Dinfty.GluingTowerLibrary` |
| `D-0530` | def | `leGlueGen` | `Dinfty.GluingTowerLibrary` |
| `D-0531` | theorem | `rawRuleGen_trans` | `Dinfty.GluingTowerLibrary` |
| `D-0532` | theorem | `occsGen_canon_mem` | `Dinfty.GluingTowerLibrary` |
| `D-0533` | theorem | `leGlueGen_refl` | `Dinfty.GluingTowerLibrary` |
| `D-0534` | instance | `inst-P` | `Dinfty.GluingTowerLibrary` |
| `D-0535` | theorem | `GlueCarGen.le_def` | `Dinfty.GluingTowerLibrary` |
| `D-0536` | theorem | `glueGen_antisymm` | `Dinfty.GluingTowerLibrary` |
| `D-0537` | theorem | `glueGen_trans` | `Dinfty.GluingTowerLibrary` |
| `D-0538` | def | `glueCarPartialOrderGen` | `Dinfty.GluingTowerLibrary` |
| `D-0539` | theorem | `hmL_of` | `Dinfty.GluingTowerLibrary` |
| `D-0540` | theorem | `hmtL_of` | `Dinfty.GluingTowerLibrary` |
| `D-0541` | theorem | `hbtEL_of` | `Dinfty.GluingTowerLibrary` |
| `D-0542` | def | `iotaGen` | `Dinfty.GluingTowerLibrary` |
| `D-0543` | theorem | `iotaGen_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0544` | theorem | `iotaGen_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0545` | theorem | `iotaGen_monotone` | `Dinfty.GluingTowerLibrary` |
| `D-0546` | def | `iotaEndPGen` | `Dinfty.GluingTowerLibrary` |
| `D-0547` | theorem | `iotaEndPGen_apply` | `Dinfty.GluingTowerLibrary` |
| `D-0548` | theorem | `iotaEndPGen_monotone` | `Dinfty.GluingTowerLibrary` |
| `D-0549` | theorem | `ite_dominate_mono` | `Dinfty.GluingTowerLibrary` |
| `D-0550` | def | `liftGen` | `Dinfty.GluingTowerLibrary` |
| `D-0551` | theorem | `liftGen_monotone` | `Dinfty.GluingTowerLibrary` |
| `D-0552` | theorem | `constHom_bot_eq` | `Dinfty.GluingTowerLibrary` |
| `D-0553` | theorem | `iotaGen_pGen_deflation` | `Dinfty.GluingTowerLibrary` |
| `D-0554` | theorem | `iotaGen_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0555` | theorem | `liftGen_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0556` | theorem | `liftGen_id` | `Dinfty.GluingTowerLibrary` |
| `D-0557` | theorem | `liftGen_top` | `Dinfty.GluingTowerLibrary` |
| `D-0558` | theorem | `rawRule_leGlue_canon` | `Dinfty.GluingTowerLibrary` |
| `D-0559` | def | `glueAAGen` | `Dinfty.GluingTowerLibrary` |
| `D-0560` | theorem | `glueAAGen_monotone` | `Dinfty.GluingTowerLibrary` |
| `D-0561` | theorem | `iotaEndPGen_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0562` | theorem | `iotaEndPGen_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0563` | theorem | `iotaGen_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0564` | theorem | `liftGen_apply` | `Dinfty.GluingTowerLibrary` |
| `D-0565` | theorem | `liftGen_eq_bot_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0566` | theorem | `liftGen_eq_id_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0567` | theorem | `liftGen_eq_top_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0568` | theorem | `liftGen_apply_iotaGen_of_not_top` | `Dinfty.GluingTowerLibrary` |
| `D-0569` | theorem | `glueAAGen_reflect` | `Dinfty.GluingTowerLibrary` |
| `D-0570` | theorem | `glueAAGen_le_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0571` | theorem | `glueAAGen_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0572` | theorem | `iotaEndPGen_constHom` | `Dinfty.GluingTowerLibrary` |
| `D-0573` | theorem | `glueAAGen_iotaGen` | `Dinfty.GluingTowerLibrary` |
| `D-0574` | theorem | `glueAAGen_pGen_deflation_tagA` | `Dinfty.GluingTowerLibrary` |
| `D-0575` | theorem | `glueAAGen_pGen_deflation_tagB` | `Dinfty.GluingTowerLibrary` |
| `D-0576` | theorem | `endP_eq_top_of_apply_bot_eq_top` | `Dinfty.GluingTowerLibrary` |
| `D-0577` | theorem | `crossTag_CA_sufficient` | `Dinfty.GluingTowerLibrary` |
| `D-0578` | abbrev | `iotaAGen` | `Dinfty.GluingTowerLibrary` |
| `D-0579` | abbrev | `iotaBGen` | `Dinfty.GluingTowerLibrary` |
| `D-0580` | abbrev | `iotaCGen` | `Dinfty.GluingTowerLibrary` |
| `D-0581` | theorem | `self_mem_occsGen` | `Dinfty.GluingTowerLibrary` |
| `D-0582` | theorem | `occs_inl_memGen` | `Dinfty.GluingTowerLibrary` |
| `D-0583` | theorem | `tagA_isoGen` | `Dinfty.GluingTowerLibrary` |
| `D-0584` | theorem | `iotaB_generic_eqGen` | `Dinfty.GluingTowerLibrary` |
| `D-0585` | theorem | `occs_iotaB_memGen` | `Dinfty.GluingTowerLibrary` |
| `D-0586` | theorem | `leGlue_tagA_tagB_iffGen` | `Dinfty.GluingTowerLibrary` |
| `D-0587` | theorem | `leGlue_tagB_tagB_iffGen` | `Dinfty.GluingTowerLibrary` |
| `D-0588` | theorem | `leGlue_tagA_tagCGen` | `Dinfty.GluingTowerLibrary` |
| `D-0589` | theorem | `leGlue_tagB_tagC_iffGen` | `Dinfty.GluingTowerLibrary` |
| `D-0590` | theorem | `not_leGlue_tagB_tagAGen` | `Dinfty.GluingTowerLibrary` |
| `D-0591` | theorem | `not_leGlue_tagC_tagAGen` | `Dinfty.GluingTowerLibrary` |
| `D-0592` | theorem | `not_leGlue_tagC_tagBGen` | `Dinfty.GluingTowerLibrary` |
| `D-0593` | theorem | `leGlue_tagC_tagC_iffGen` | `Dinfty.GluingTowerLibrary` |
| `D-0594` | theorem | `leGlue_tagC_tagB_top_iffGen` | `Dinfty.GluingTowerLibrary` |
| `D-0595` | def | `phiGen` | `Dinfty.GluingTowerLibrary` |
| `D-0596` | theorem | `leGlueGen_tagC_iff_le_phiGen` | `Dinfty.GluingTowerLibrary` |
| `D-0597` | theorem | `ne_bot_of_canon_tagBGen` | `Dinfty.GluingTowerLibrary` |
| `D-0598` | theorem | `ne_bot_of_canon_tagCGen` | `Dinfty.GluingTowerLibrary` |
| `D-0599` | theorem | `phiGen_monotone` | `Dinfty.GluingTowerLibrary` |
| `D-0600` | theorem | `phiGen_mem_upperBounds_image` | `Dinfty.GluingTowerLibrary` |
| `D-0601` | theorem | `leGlue_tagA_tagB_topGen` | `Dinfty.GluingTowerLibrary` |
| `D-0602` | def | `tagCGen` | `Dinfty.GluingTowerLibrary` |
| `D-0603` | theorem | `tagCGen_val_of_generic` | `Dinfty.GluingTowerLibrary` |
| `D-0604` | def | `skelG3Gen` | `Dinfty.GluingTowerLibrary` |
| `D-0605` | theorem | `skelG3Gen_val` | `Dinfty.GluingTowerLibrary` |
| `D-0606` | def | `tagAGen` | `Dinfty.GluingTowerLibrary` |
| `D-0607` | theorem | `tagAGen_val` | `Dinfty.GluingTowerLibrary` |
| `D-0608` | theorem | `skelG3Gen_mem_upperBounds_of_pureAB` | `Dinfty.GluingTowerLibrary` |
| `D-0609` | theorem | `tagC_generic_not_isLUB_of_pureAB_hasB` | `Dinfty.GluingTowerLibrary` |
| `D-0610` | theorem | `tagC_generic_not_isLUB_of_pureA` | `Dinfty.GluingTowerLibrary` |
| `D-0611` | theorem | `exists_tagC_or_skelG3_dominating` | `Dinfty.GluingTowerLibrary` |
| `D-0612` | theorem | `tagCGen_t0_mem_upperBounds` | `Dinfty.GluingTowerLibrary` |
| `D-0613` | theorem | `tagCGen_isCompactElement` | `Dinfty.GluingTowerLibrary` |
| `D-0614` | theorem | `tagAGen_isLUB_image` | `Dinfty.GluingTowerLibrary` |
| `D-0615` | theorem | `isCompactElement_of_tagAGen_isCompactElement` | `Dinfty.GluingTowerLibrary` |
| `D-0616` | def | `glueBaseGenEquiv` | `Dinfty.GluingTowerLibrary` |
| `D-0617` | def | `mapGlueBaseGen` | `Dinfty.GluingTowerLibrary` |
| `D-0618` | theorem | `mapGlueBaseGen_inl` | `Dinfty.GluingTowerLibrary` |
| `D-0619` | theorem | `mapGlueBaseGen_inr_inl` | `Dinfty.GluingTowerLibrary` |
| `D-0620` | theorem | `mapGlueBaseGen_inr_inr` | `Dinfty.GluingTowerLibrary` |
| `D-0621` | theorem | `mapGlueBaseGen_injective` | `Dinfty.GluingTowerLibrary` |
| `D-0622` | theorem | `canonGen_map` | `Dinfty.GluingTowerLibrary` |
| `D-0623` | theorem | `rawRuleGen_map` | `Dinfty.GluingTowerLibrary` |
| `D-0624` | theorem | `occsGen_map` | `Dinfty.GluingTowerLibrary` |
| `D-0625` | theorem | `leGlueGen_map_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0626` | def | `glueCarGenEquiv` | `Dinfty.GluingTowerLibrary` |
| `D-0627` | def | `glueCarGenOrderIso` | `Dinfty.GluingTowerLibrary` |
| `D-0628` | theorem | `_root_.IsCompactElement.orderIso` | `Dinfty.GluingTowerLibrary` |
| `D-0629` | theorem | `leGlue_tagA_skelG3` | `Dinfty.GluingTowerLibrary` |
| `D-0630` | theorem | `leGlue_tagB_skelG3` | `Dinfty.GluingTowerLibrary` |
| `D-0631` | theorem | `leGlue_tagC_skelG3_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0632` | theorem | `incGlue_skelG3_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0633` | theorem | `glueCar_cases` | `Dinfty.GluingTowerLibrary` |
| `D-0634` | theorem | `not_hasUniqueDownCover_of_two_covers` | `Dinfty.GluingTowerLibrary` |
| `D-0635` | theorem | `joinIrred_top` | `Dinfty.GluingTowerLibrary` |
| `D-0636` | theorem | `endPId_ne_stepMap` | `Dinfty.GluingTowerLibrary` |
| `D-0637` | theorem | `endPId_not_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0638` | theorem | `coatomOf_ne_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0639` | theorem | `covers_glueB_coatomOf_glueB_top` | `Dinfty.GluingTowerLibrary` |
| `D-0640` | theorem | `not_hasUniqueDownCover_glueB_top` | `Dinfty.GluingTowerLibrary` |
| `D-0641` | theorem | `card_joinIrred_eq_succ_of_ne_top` | `Dinfty.GluingTowerLibrary` |
| `D-0642` | theorem | `card_joinIrred_and_ne_eq_of_not_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0643` | def | `jiGlueCarSuccEquiv` | `Dinfty.GluingTowerLibrary` |
| `D-0644` | theorem | `card_joinIrred_glueCar_gen` | `Dinfty.GluingTowerLibrary` |
| `D-0645` | theorem | `card_joinIrred_glueCar_endP_id` | `Dinfty.GluingTowerLibrary` |
| `D-0646` | theorem | `leGlue_tagA_skelG1_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0647` | theorem | `leGlue_skelG1_tagA_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0648` | theorem | `leGlue_skelG1_tagB` | `Dinfty.GluingTowerLibrary` |
| `D-0649` | theorem | `leGlue_skelG1_tagC` | `Dinfty.GluingTowerLibrary` |
| `D-0650` | theorem | `incGlue_skelG1_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0651` | theorem | `incGlue_tagA_of_le` | `Dinfty.GluingTowerLibrary` |
| `D-0652` | theorem | `incGlue_tagC_of_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0653` | theorem | `isGLB_inc_skelG3` | `Dinfty.GluingTowerLibrary` |
| `D-0654` | theorem | `isLUB_inc_skelG1` | `Dinfty.GluingTowerLibrary` |
| `D-0655` | def | `branchF1` | `Dinfty.GluingTowerLibrary` |
| `D-0656` | def | `branchF2` | `Dinfty.GluingTowerLibrary` |
| `D-0657` | theorem | `branchF1_apply_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0658` | theorem | `branchF2_apply_bot` | `Dinfty.GluingTowerLibrary` |
| `D-0659` | theorem | `branchF1_ne_branchF2` | `Dinfty.GluingTowerLibrary` |
| `D-0660` | theorem | `isLUB_ne_bot_ne_top_coatomOf` | `Dinfty.GluingTowerLibrary` |
| `D-0661` | theorem | `incGlue_tagA_of_not_le` | `Dinfty.GluingTowerLibrary` |
| `D-0662` | theorem | `isLUB_inc_tagA_of_not_le` | `Dinfty.GluingTowerLibrary` |
| `D-0663` | theorem | `glueA_ne_isLUB_inc_tagA_of_not_le` | `Dinfty.GluingTowerLibrary` |
| `D-0664` | theorem | `isGLB_ne_bot_ne_top_atomOf` | `Dinfty.GluingTowerLibrary` |
| `D-0665` | theorem | `incGlue_tagC_of_not_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0666` | theorem | `isGLB_inc_tagC_of_not_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0667` | theorem | `glueC_ne_isGLB_inc_tagC_of_not_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0668` | theorem | `incGlue_tagB_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0669` | theorem | `isLUB_inc_tagB_of_ne_empty` | `Dinfty.GluingTowerLibrary` |
| `D-0670` | theorem | `isGLB_inc_tagB_of_ne_empty` | `Dinfty.GluingTowerLibrary` |
| `D-0671` | theorem | `glueBt_ne_isGLB_of_glueC_inc` | `Dinfty.GluingTowerLibrary` |
| `D-0672` | theorem | `isLUB_inc_tagB_of_inc_empty` | `Dinfty.GluingTowerLibrary` |
| `D-0673` | theorem | `glueC_inf_glueBt_atomOf_eq_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0674` | theorem | `isGLB_inc_glueC_kappa_eq_glueBt_atomOf_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0675` | theorem | `glueB_atomOf_roundtrip_iff_of_not_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0676` | theorem | `glueB_atomOf_not_roundtrip_of_ge` | `Dinfty.GluingTowerLibrary` |
| `D-0677` | theorem | `card_joinIrred_eq_succ_of_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0678` | theorem | `card_joinIrred_glueCar_gen_of_joinIrred` | `Dinfty.GluingTowerLibrary` |
| `D-0679` | theorem | `joinIrred_constHom_iff` | `Dinfty.GluingTowerLibrary` |
| `D-0680` | theorem | `card_joinIrred_glueCar_endP_constHom` | `Dinfty.GluingTowerLibrary` |
| `D-0681` | section | `§ The canon-fixed condition as a property, not a decidable equation` | `Dinfty.CanonFixed` |
| `D-0682` | def | `Fixed` | `Dinfty.CanonFixed` |
| `D-0683` | theorem | `fixed_inl` | `Dinfty.CanonFixed` |
| `D-0684` | theorem | `fixed_inrl` | `Dinfty.CanonFixed` |
| `D-0685` | theorem | `fixed_inrr` | `Dinfty.CanonFixed` |
| `D-0686` | theorem | `fixed_iff` | `Dinfty.CanonFixed` |
| `D-0687` | def | `GlueCarFix` | `Dinfty.CanonFixed` |
| `D-0688` | def | `equivGlueCarGen` | `Dinfty.CanonFixed` |
| `D-0689` | theorem | `equivGlueCarGen_val` | `Dinfty.CanonFixed` |
| `D-0690` | theorem | `equivGlueCarGen_symm_val` | `Dinfty.CanonFixed` |
| `D-0691` | def | `instBridge` | `Dinfty.CanonFixed` |
| `D-0692` | theorem | `equivGlueCarGen_leGlueGen` | `Dinfty.CanonFixed` |
| `D-0693` | section | `§ `GlueAAGenReflect`, migrated to a constant marked point` | `Dinfty.GlueAAGenReflectM` |
| `D-0694` | section | `§ The marked point is a constant` | `Dinfty.GlueAAGenReflectM` |
| `D-0695` | theorem | `hmM_of` | `Dinfty.GlueAAGenReflectM` |
| `D-0696` | theorem | `hmtM_of` | `Dinfty.GlueAAGenReflectM` |
| `D-0697` | section | `§ `pGenM` : the ep-pair projection at a constant marked point` | `Dinfty.GlueAAGenReflectM` |
| `D-0698` | def | `pGenM` | `Dinfty.GlueAAGenReflectM` |
| `D-0699` | def | `iotaGenM` | `Dinfty.GlueAAGenReflectM` |
| `D-0700` | theorem | `pGenM_section` | `Dinfty.GlueAAGenReflectM` |
| `D-0701` | theorem | `iotaGenM_le_iff` | `Dinfty.GlueAAGenReflectM` |
| `D-0702` | theorem | `iotaGenM_injective` | `Dinfty.GlueAAGenReflectM` |
| `D-0703` | theorem | `iotaGenM_monotone` | `Dinfty.GlueAAGenReflectM` |
| `D-0704` | theorem | `pGenM_deflation` | `Dinfty.GlueAAGenReflectM` |
| `D-0705` | theorem | `pGenM_monotone` | `Dinfty.GlueAAGenReflectM` |
| `D-0706` | section | `§ The next level's marked point` | `Dinfty.GlueAAGenReflectM` |
| `D-0707` | def | `midM` | `Dinfty.GlueAAGenReflectM` |
| `D-0708` | theorem | `midM_ne_bot` | `Dinfty.GlueAAGenReflectM` |
| `D-0709` | theorem | `iotaGenM_ne_top` | `Dinfty.GlueAAGenReflectM` |
| `D-0710` | theorem | `midM_ne_top` | `Dinfty.GlueAAGenReflectM` |
| `D-0711` | section | `§ `midM` is the ONLY possible next marked point` | `Dinfty.GlueAAGenReflectM` |
| `D-0712` | theorem | `midM_unique` | `Dinfty.GlueAAGenReflectM` |
| `D-0713` | theorem | `midM_ne_skelL` | `Dinfty.GlueAAGenReflectM` |
| `D-0714` | section | `§ `iotaEndPGenM` and `liftGenM`` | `Dinfty.GlueAAGenReflectM` |
| `D-0715` | def | `iotaEndPGenM` | `Dinfty.GlueAAGenReflectM` |
| `D-0716` | theorem | `iotaEndPGenM_apply` | `Dinfty.GlueAAGenReflectM` |
| `D-0717` | theorem | `iotaEndPGenM_monotone` | `Dinfty.GlueAAGenReflectM` |
| `D-0718` | def | `liftGenM` | `Dinfty.GlueAAGenReflectM` |
| `D-0719` | theorem | `liftGenM_monotone` | `Dinfty.GlueAAGenReflectM` |
| `D-0720` | section | `§ Boundary values` | `Dinfty.GlueAAGenReflectM` |
| `D-0721` | theorem | `iotaGenM_bot` | `Dinfty.GlueAAGenReflectM` |
| `D-0722` | theorem | `iotaEndPGenM_bot` | `Dinfty.GlueAAGenReflectM` |
| `D-0723` | theorem | `liftGenM_bot` | `Dinfty.GlueAAGenReflectM` |
| `D-0724` | theorem | `liftGenM_mid` | `Dinfty.GlueAAGenReflectM` |
| `D-0725` | theorem | `liftGenM_top` | `Dinfty.GlueAAGenReflectM` |
| `D-0726` | theorem | `iotaEndPGenM_le_iff` | `Dinfty.GlueAAGenReflectM` |
| `D-0727` | theorem | `liftGenM_apply` | `Dinfty.GlueAAGenReflectM` |
| `D-0728` | theorem | `liftGenM_eq_bot_iff` | `Dinfty.GlueAAGenReflectM` |
| `D-0729` | theorem | `liftGenM_eq_mid_iff` | `Dinfty.GlueAAGenReflectM` |
| `D-0730` | theorem | `liftGenM_eq_top_iff` | `Dinfty.GlueAAGenReflectM` |
| `D-0731` | theorem | `liftGenM_apply_iotaGenM_of_not_top` | `Dinfty.GlueAAGenReflectM` |
| `D-0732` | theorem | `iotaEndPGenM_mid_le` | `Dinfty.GlueAAGenReflectM` |
| `D-0733` | section | `§ `glueAAGenM`` | `Dinfty.GlueAAGenReflectM` |
| `D-0734` | def | `glueAAGenM` | `Dinfty.GlueAAGenReflectM` |
| `D-0735` | theorem | `glueAAGenM_monotone` | `Dinfty.GlueAAGenReflectM` |
| `D-0736` | theorem | `glueAAGenM_reflect` | `Dinfty.GlueAAGenReflectM` |
| `D-0737` | theorem | `glueAAGenM_le_iff` | `Dinfty.GlueAAGenReflectM` |
| `D-0738` | theorem | `glueAAGenM_injective` | `Dinfty.GlueAAGenReflectM` |
| `D-0739` | section | `§ Two negative checks` | `Dinfty.GlueAAGenReflectM` |
| `D-0740` | def | `pGenBad` | `Dinfty.GlueAAGenReflectM` |
| `D-0741` | theorem | `pGenBad_not_monotone` | `Dinfty.GlueAAGenReflectM` |
| `D-0742` | theorem | `skelL_not_admissible` | `Dinfty.GlueAAGenReflectM` |
| `D-0743` | section | `§ Which of the two obligations `skelL` fails` | `Dinfty.GlueAAGenReflectM` |
| `D-0744` | theorem | `skelL_satisfies_hup` | `Dinfty.GlueAAGenReflectM` |
| `D-0745` | theorem | `skelL_fails_hdown` | `Dinfty.GlueAAGenReflectM` |
| `D-0746` | section | `§ The three-way fork dissolves: `hdown` alone forces tag-`A`` | `Dinfty.GlueAAGenReflectM` |
| `D-0747` | theorem | `tagA_of_hdown_at_mid` | `Dinfty.GlueAAGenReflectM` |
| `D-0748` | theorem | `not_hdown_of_tagB` | `Dinfty.GlueAAGenReflectM` |
| `D-0749` | theorem | `not_hdown_of_tagC` | `Dinfty.GlueAAGenReflectM` |
| `D-0750` | theorem | `canon_tagC_self` | `Dinfty.GlueAAGenReflectM` |
| `D-0751` | section | `§ Specialised to the migration's own `hdown`` | `Dinfty.GlueAAGenReflectM` |
| `D-0752` | theorem | `tagA_of_hdownM` | `Dinfty.GlueAAGenReflectM` |
| `D-0753` | theorem | `skelL_fails_hdown_of_general` | `Dinfty.GlueAAGenReflectM` |
| `D-0754` | theorem | `muM_eq_tagA_mid` | `Dinfty.GlueAAGenReflectM` |
| `D-0755` | theorem | `muM_eq_skelG1` | `Dinfty.GlueAAGenReflectM` |
| `D-0756` | section | `§ Non-vacuity of the two excluded branches` | `Dinfty.GlueAAGenReflectM` |
| `D-0757` | theorem | `canon_tagC_top` | `Dinfty.GlueAAGenReflectM` |
| `D-0758` | theorem | `tagC_top_fails_hdown` | `Dinfty.GlueAAGenReflectM` |
| `D-0759` | section | `§ The same theorem in the `Gen` world — the scoping draft's statement, verbatim` | `Dinfty.GlueAAGenReflectM` |
| `D-0760` | theorem | `tagA_of_hdownGen_at_mid` | `Dinfty.GlueAAGenReflectM` |
| `D-0761` | theorem | `not_hdownGen_of_tagB` | `Dinfty.GlueAAGenReflectM` |
| `D-0762` | theorem | `not_hdownGen_of_tagC` | `Dinfty.GlueAAGenReflectM` |
| `D-0763` | section | `§ Closing the normalized migration: the lemmas `GlueAAGenReflectM` does not have` | `Dinfty.MigrationCloseout` |
| `D-0764` | theorem | `pGenM_top` | `Dinfty.MigrationCloseout` |
| `D-0765` | theorem | `iotaEndPGenM_constHom` | `Dinfty.MigrationCloseout` |
| `D-0766` | theorem | `glueAAGenM_iotaGenM` | `Dinfty.MigrationCloseout` |
| `D-0767` | theorem | `glueAAGenM_pGenM_deflation_tagA` | `Dinfty.MigrationCloseout` |
| `D-0768` | theorem | `glueAAGenM_pGenM_deflation_tagB` | `Dinfty.MigrationCloseout` |
| `D-0769` | theorem | `crossTag_CA_sufficientM` | `Dinfty.MigrationCloseout` |
| `D-0770` | structure | `TowerLevel` | `Dinfty.SierpinskiApplication` |
| `D-0771` | def | `towerLevel0` | `Dinfty.SierpinskiApplication` |
| `D-0772` | def | `towerLevelSucc` | `Dinfty.SierpinskiApplication` |
| `D-0773` | def | `towerLevel` | `Dinfty.SierpinskiApplication` |
| `D-0774` | def | `D` | `Dinfty.SierpinskiApplication` |
| `D-0775` | instance | `instDecidableEqD` | `Dinfty.SierpinskiApplication` |
| `D-0776` | instance | `instLatticeD` | `Dinfty.SierpinskiApplication` |
| `D-0777` | instance | `instBoundedOrderD` | `Dinfty.SierpinskiApplication` |
| `D-0778` | instance | `instFintypeD` | `Dinfty.SierpinskiApplication` |
| `D-0779` | instance | `instNontrivialD` | `Dinfty.SierpinskiApplication` |
| `D-0780` | def | `dMid` | `Dinfty.SierpinskiApplication` |
| `D-0781` | theorem | `dMid_ne_bot` | `Dinfty.SierpinskiApplication` |
| `D-0782` | theorem | `dMid_ne_top` | `Dinfty.SierpinskiApplication` |
| `D-0783` | def | `markedPt` | `Dinfty.SierpinskiApplication` |
| `D-0784` | theorem | `markedPt_apply` | `Dinfty.SierpinskiApplication` |
| `D-0785` | theorem | `markedPt_ne_bot` | `Dinfty.SierpinskiApplication` |
| `D-0786` | theorem | `markedPt_ne_top` | `Dinfty.SierpinskiApplication` |
| `D-0787` | instance | `finThreeUniqueAtomCoatom` | `Dinfty.SierpinskiApplication` |
| `D-0788` | theorem | `D_marked_point_nondegenerate` | `Dinfty.SierpinskiApplication` |
| `D-0789` | theorem | `D_has_interior_point` | `Dinfty.SierpinskiApplication` |
| `D-0790` | def | `realUniqueAtomCoatom` | `Dinfty.SierpinskiApplication` |
| `D-0791` | theorem | `D0_rigid` | `Dinfty.SierpinskiApplication` |
| `D-0792` | theorem | `D_top_hasUniqueDownCover` | `Dinfty.SierpinskiApplication` |
| `D-0793` | theorem | `D_bot_hasUniqueUpCover` | `Dinfty.SierpinskiApplication` |
| `D-0794` | theorem | `D_has_second_joinIrred` | `Dinfty.SierpinskiApplication` |
| `D-0795` | theorem | `D_card_ge_three` | `Dinfty.SierpinskiApplication` |
| `D-0796` | theorem | `D_mid_joinIrred` | `Dinfty.SierpinskiApplication` |
| `D-0797` | theorem | `card_joinIrred_D_succ` | `Dinfty.SierpinskiApplication` |
| `D-0798` | theorem | `D_up_transfer` | `Dinfty.SierpinskiApplication` |
| `D-0799` | def | `downCard` | `Dinfty.SierpinskiApplication` |
| `D-0800` | def | `upCard` | `Dinfty.SierpinskiApplication` |
| `D-0801` | theorem | `downCard_map` | `Dinfty.SierpinskiApplication` |
| `D-0802` | theorem | `upCard_map` | `Dinfty.SierpinskiApplication` |
| `D-0803` | theorem | `endPFin3_inv_injective` | `Dinfty.SierpinskiApplication` |
| `D-0804` | theorem | `H0_rigid_fixes` | `Dinfty.SierpinskiApplication` |
| `D-0805` | theorem | `H0_rigid` | `Dinfty.SierpinskiApplication` |
| `D-0806` | theorem | `D1_rigid` | `Dinfty.SierpinskiApplication` |
| `D-0807` | theorem | `D0_J_connected` | `Dinfty.SierpinskiApplication` |
| `D-0808` | theorem | `D_J_connected` | `Dinfty.SierpinskiApplication` |
| `D-0809` | theorem | `D_down_transfer` | `Dinfty.SierpinskiApplication` |
| `D-0810` | instance | `realGluingTower` | `Dinfty.SierpinskiApplication` |
| `D-0811` | instance | `realGluingTowerUp` | `Dinfty.SierpinskiApplication` |
| `D-0812` | instance | `realGluingTowerDown` | `Dinfty.SierpinskiApplication` |
| `D-0813` | theorem | `D_all_rigid` | `Dinfty.SierpinskiApplication` |
| `D-0814` | abbrev | `Plane` | `Dinfty.SierpinskiApplication` |
| `D-0815` | def | `vA` | `Dinfty.SierpinskiApplication` |
| `D-0816` | def | `vB` | `Dinfty.SierpinskiApplication` |
| `D-0817` | def | `vC` | `Dinfty.SierpinskiApplication` |
| `D-0818` | def | `fA` | `Dinfty.SierpinskiApplication` |
| `D-0819` | def | `fB` | `Dinfty.SierpinskiApplication` |
| `D-0820` | def | `fC` | `Dinfty.SierpinskiApplication` |
| `D-0821` | theorem | `dist_fA` | `Dinfty.SierpinskiApplication` |
| `D-0822` | theorem | `dist_fB` | `Dinfty.SierpinskiApplication` |
| `D-0823` | theorem | `dist_fC` | `Dinfty.SierpinskiApplication` |
| `D-0824` | theorem | `lipschitzWith_fA` | `Dinfty.SierpinskiApplication` |
| `D-0825` | theorem | `lipschitzWith_fB` | `Dinfty.SierpinskiApplication` |
| `D-0826` | theorem | `lipschitzWith_fC` | `Dinfty.SierpinskiApplication` |
| `D-0827` | def | `Delta` | `Dinfty.SierpinskiApplication` |
| `D-0828` | theorem | `isClosed_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0829` | theorem | `isBounded_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0830` | theorem | `isCompact_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0831` | theorem | `nonempty_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0832` | theorem | `vA_mem_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0833` | theorem | `vB_mem_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0834` | theorem | `vC_mem_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0835` | theorem | `image_fA_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0836` | theorem | `image_fB_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0837` | theorem | `image_fC_Delta` | `Dinfty.SierpinskiApplication` |
| `D-0838` | theorem | `touch_fA_fB` | `Dinfty.SierpinskiApplication` |
| `D-0839` | theorem | `touch_fA_fC` | `Dinfty.SierpinskiApplication` |
| `D-0840` | theorem | `touch_fB_fC` | `Dinfty.SierpinskiApplication` |
| `D-0841` | section | `§ The Hutchinson operator: a `(1/2)`-contraction on `NonemptyCompacts Plane`` | `Dinfty.SierpinskiApplication` |
| `D-0842` | theorem | `infDist_image_le_of_lipschitz` | `Dinfty.SierpinskiApplication` |
| `D-0843` | theorem | `hausdorffDist_image_le_of_lipschitz` | `Dinfty.SierpinskiApplication` |
| `D-0844` | def | `mapNC` | `Dinfty.SierpinskiApplication` |
| `D-0845` | theorem | `coe_mapNC` | `Dinfty.SierpinskiApplication` |
| `D-0846` | theorem | `lipschitzWith_mapNC` | `Dinfty.SierpinskiApplication` |
| `D-0847` | theorem | `dist_sup_le_max` | `Dinfty.SierpinskiApplication` |
| `D-0848` | def | `Hutchinson` | `Dinfty.SierpinskiApplication` |
| `D-0849` | theorem | `hutchinson_dist_le` | `Dinfty.SierpinskiApplication` |
| `D-0850` | theorem | `lipschitzWith_hutchinson` | `Dinfty.SierpinskiApplication` |
| `D-0851` | theorem | `contractingWith_hutchinson` | `Dinfty.SierpinskiApplication` |
| `D-0852` | instance | `inst-Nonempty` | `Dinfty.SierpinskiApplication` |
| `D-0853` | def | `GammaNC` | `Dinfty.SierpinskiApplication` |
| `D-0854` | theorem | `GammaNC_fixed` | `Dinfty.SierpinskiApplication` |
| `D-0855` | def | `Gamma` | `Dinfty.SierpinskiApplication` |
| `D-0856` | theorem | `isCompact_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-0857` | theorem | `nonempty_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-0858` | theorem | `Gamma_self_similar` | `Dinfty.SierpinskiApplication` |
| `D-0859` | def | `iotaD` | `Dinfty.SierpinskiApplication` |
| `D-0860` | theorem | `iotaD_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-0861` | theorem | `iotaD_injective` | `Dinfty.SierpinskiApplication` |
| `D-0862` | theorem | `iotaD_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0863` | theorem | `iotaD_lt_iff` | `Dinfty.SierpinskiApplication` |
| `D-0864` | theorem | `iotaD_strictMono` | `Dinfty.SierpinskiApplication` |
| `D-0865` | theorem | `iotaD_sup` | `Dinfty.SierpinskiApplication` |
| `D-0866` | theorem | `iotaD_inf` | `Dinfty.SierpinskiApplication` |
| `D-0867` | def | `sigmaD` | `Dinfty.SierpinskiApplication` |
| `D-0868` | theorem | `sigmaD_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-0869` | theorem | `sigmaD_injective` | `Dinfty.SierpinskiApplication` |
| `D-0870` | theorem | `sigmaD_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0871` | theorem | `sigmaD_lt_iff` | `Dinfty.SierpinskiApplication` |
| `D-0872` | theorem | `sigmaD_strictMono` | `Dinfty.SierpinskiApplication` |
| `D-0873` | theorem | `sigmaD_top` | `Dinfty.SierpinskiApplication` |
| `D-0874` | theorem | `sigmaD_bot_eq_iotaD_bot` | `Dinfty.SierpinskiApplication` |
| `D-0875` | def | `iotaLe` | `Dinfty.SierpinskiApplication` |
| `D-0876` | theorem | `iotaLe_self` | `Dinfty.SierpinskiApplication` |
| `D-0877` | theorem | `iotaLe_succ` | `Dinfty.SierpinskiApplication` |
| `D-0878` | theorem | `iotaLe_trans` | `Dinfty.SierpinskiApplication` |
| `D-0879` | theorem | `iotaLe_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-0880` | theorem | `iotaLe_injective` | `Dinfty.SierpinskiApplication` |
| `D-0881` | theorem | `iotaLe_sup` | `Dinfty.SierpinskiApplication` |
| `D-0882` | theorem | `iotaLe_inf` | `Dinfty.SierpinskiApplication` |
| `D-0883` | section | `§ The colimit relation on `Σ k, D k`` | `Dinfty.SierpinskiApplication` |
| `D-0884` | def | `DInftyRel` | `Dinfty.SierpinskiApplication` |
| `D-0885` | theorem | `chase_eq_level_indep` | `Dinfty.SierpinskiApplication` |
| `D-0886` | theorem | `chase_eq_of_rel` | `Dinfty.SierpinskiApplication` |
| `D-0887` | theorem | `DInftyRel_refl` | `Dinfty.SierpinskiApplication` |
| `D-0888` | theorem | `DInftyRel_symm` | `Dinfty.SierpinskiApplication` |
| `D-0889` | theorem | `DInftyRel_trans` | `Dinfty.SierpinskiApplication` |
| `D-0890` | instance | `dInftySetoid` | `Dinfty.SierpinskiApplication` |
| `D-0891` | def | `DInfty` | `Dinfty.SierpinskiApplication` |
| `D-0892` | section | `§ Canonical inclusions `D_k ↪ D_∞`` | `Dinfty.SierpinskiApplication` |
| `D-0893` | def | `toD` | `Dinfty.SierpinskiApplication` |
| `D-0894` | theorem | `toD_iotaD` | `Dinfty.SierpinskiApplication` |
| `D-0895` | theorem | `toD_injective` | `Dinfty.SierpinskiApplication` |
| `D-0896` | theorem | `toD_surjective` | `Dinfty.SierpinskiApplication` |
| `D-0897` | section | `§ The order on `D_∞`` | `Dinfty.SierpinskiApplication` |
| `D-0898` | def | `DInftyLeRel` | `Dinfty.SierpinskiApplication` |
| `D-0899` | theorem | `DInftyLeRel_iff_atLevel` | `Dinfty.SierpinskiApplication` |
| `D-0900` | theorem | `DInftyLeRel_congr` | `Dinfty.SierpinskiApplication` |
| `D-0901` | def | `DInftyLE` | `Dinfty.SierpinskiApplication` |
| `D-0902` | instance | `inst-LE` | `Dinfty.SierpinskiApplication` |
| `D-0903` | theorem | `toD_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-0904` | instance | `inst-PartialOrder` | `Dinfty.SierpinskiApplication` |
| `D-0905` | theorem | `toD_le_iff'` | `Dinfty.SierpinskiApplication` |
| `D-0906` | theorem | `toD_strictMono` | `Dinfty.SierpinskiApplication` |
| `D-0907` | section | `§ Giving `D_∞` a `Lattice` structure -- 2026-08-20 session` | `Dinfty.SierpinskiApplication` |
| `D-0908` | theorem | `toD_iotaLe` | `Dinfty.SierpinskiApplication` |
| `D-0909` | def | `DInftySupRep` | `Dinfty.SierpinskiApplication` |
| `D-0910` | theorem | `DInftySupRep_atLevel` | `Dinfty.SierpinskiApplication` |
| `D-0911` | theorem | `DInftySupRep_congr` | `Dinfty.SierpinskiApplication` |
| `D-0912` | def | `DInftySup` | `Dinfty.SierpinskiApplication` |
| `D-0913` | instance | `inst-Max` | `Dinfty.SierpinskiApplication` |
| `D-0914` | theorem | `toD_sup` | `Dinfty.SierpinskiApplication` |
| `D-0915` | theorem | `toD_sup'` | `Dinfty.SierpinskiApplication` |
| `D-0916` | theorem | `DInftySup_le_left` | `Dinfty.SierpinskiApplication` |
| `D-0917` | theorem | `DInftySup_le_right` | `Dinfty.SierpinskiApplication` |
| `D-0918` | theorem | `DInftySup_le` | `Dinfty.SierpinskiApplication` |
| `D-0919` | instance | `inst-SemilatticeSup` | `Dinfty.SierpinskiApplication` |
| `D-0920` | def | `DInftyInfRep` | `Dinfty.SierpinskiApplication` |
| `D-0921` | theorem | `DInftyInfRep_atLevel` | `Dinfty.SierpinskiApplication` |
| `D-0922` | theorem | `DInftyInfRep_congr` | `Dinfty.SierpinskiApplication` |
| `D-0923` | def | `DInftyInf` | `Dinfty.SierpinskiApplication` |
| `D-0924` | instance | `inst-Min` | `Dinfty.SierpinskiApplication` |
| `D-0925` | theorem | `toD_inf` | `Dinfty.SierpinskiApplication` |
| `D-0926` | theorem | `toD_inf'` | `Dinfty.SierpinskiApplication` |
| `D-0927` | theorem | `DInftyInf_le_left` | `Dinfty.SierpinskiApplication` |
| `D-0928` | theorem | `DInftyInf_le_right` | `Dinfty.SierpinskiApplication` |
| `D-0929` | theorem | `DInftyLe_inf` | `Dinfty.SierpinskiApplication` |
| `D-0930` | instance | `inst-SemilatticeInf` | `Dinfty.SierpinskiApplication` |
| `D-0931` | instance | `inst-Lattice` | `Dinfty.SierpinskiApplication` |
| `D-0932` | def | `pD` | `Dinfty.SierpinskiApplication` |
| `D-0933` | theorem | `pD_iotaD` | `Dinfty.SierpinskiApplication` |
| `D-0934` | theorem | `pD_deflation` | `Dinfty.SierpinskiApplication` |
| `D-0935` | theorem | `pD_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0936` | theorem | `pD_top` | `Dinfty.SierpinskiApplication` |
| `D-0937` | def | `DBilimit` | `Dinfty.SierpinskiApplication` |
| `D-0938` | instance | `inst-PartialOrder` | `Dinfty.SierpinskiApplication` |
| `D-0939` | def | `topSeq` | `Dinfty.SierpinskiApplication` |
| `D-0940` | instance | `inst-Nonempty` | `Dinfty.SierpinskiApplication` |
| `D-0941` | instance | `completeLatticeD` | `Dinfty.SierpinskiApplication` |
| `D-0942` | theorem | `pD_sSup_image` | `Dinfty.SierpinskiApplication` |
| `D-0943` | theorem | `DBilimit_directed_image` | `Dinfty.SierpinskiApplication` |
| `D-0944` | theorem | `DBilimit.exists_isLUB_of_directedOn` | `Dinfty.SierpinskiApplication` |
| `D-0945` | instance | `inst-TopologicalSpace` | `Dinfty.SierpinskiApplication` |
| `D-0946` | instance | `inst-IsScott` | `Dinfty.SierpinskiApplication` |
| `D-0947` | example | `example-T0Space` | `Dinfty.SierpinskiApplication` |
| `D-0948` | example | `example-Set` | `Dinfty.SierpinskiApplication` |
| `D-0949` | def | `pLe` | `Dinfty.SierpinskiApplication` |
| `D-0950` | theorem | `pLe_self` | `Dinfty.SierpinskiApplication` |
| `D-0951` | theorem | `pLe_succ` | `Dinfty.SierpinskiApplication` |
| `D-0952` | theorem | `pLe_pD_comm` | `Dinfty.SierpinskiApplication` |
| `D-0953` | def | `seqOf` | `Dinfty.SierpinskiApplication` |
| `D-0954` | theorem | `seqOf_compat` | `Dinfty.SierpinskiApplication` |
| `D-0955` | theorem | `seqOf_iotaD_step` | `Dinfty.SierpinskiApplication` |
| `D-0956` | theorem | `seqOf_iotaLe_invariant` | `Dinfty.SierpinskiApplication` |
| `D-0957` | theorem | `seqOf_congr` | `Dinfty.SierpinskiApplication` |
| `D-0958` | def | `toDBilimit` | `Dinfty.SierpinskiApplication` |
| `D-0959` | theorem | `toDBilimit_toD` | `Dinfty.SierpinskiApplication` |
| `D-0960` | theorem | `seqOf_eq_iotaLe` | `Dinfty.SierpinskiApplication` |
| `D-0961` | theorem | `toDBilimit_injective` | `Dinfty.SierpinskiApplication` |
| `D-0962` | theorem | `pLe_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0963` | theorem | `seqOf_monotone_atLevel` | `Dinfty.SierpinskiApplication` |
| `D-0964` | theorem | `toDBilimit_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0965` | theorem | `toDBilimit_reflects_le` | `Dinfty.SierpinskiApplication` |
| `D-0966` | theorem | `toDBilimit_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-0967` | def | `toDBilimitEmb` | `Dinfty.SierpinskiApplication` |
| `D-0968` | def | `iotaEndP` | `Dinfty.SierpinskiApplication` |
| `D-0969` | def | `pEndP` | `Dinfty.SierpinskiApplication` |
| `D-0970` | theorem | `pEndP_iotaEndP` | `Dinfty.SierpinskiApplication` |
| `D-0971` | theorem | `iotaEndP_pEndP_deflation` | `Dinfty.SierpinskiApplication` |
| `D-0972` | theorem | `iotaEndP_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0973` | theorem | `pEndP_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0974` | def | `EndPBilimit` | `Dinfty.SierpinskiApplication` |
| `D-0975` | instance | `inst-PartialOrder` | `Dinfty.SierpinskiApplication` |
| `D-0976` | def | `insertAtLevel` | `Dinfty.SierpinskiApplication` |
| `D-0977` | theorem | `insertAtLevel_iotaD` | `Dinfty.SierpinskiApplication` |
| `D-0978` | theorem | `insertAtLevel_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0979` | def | `toEndPBilimitAt` | `Dinfty.SierpinskiApplication` |
| `D-0980` | def | `toEndPBilimit` | `Dinfty.SierpinskiApplication` |
| `D-0981` | theorem | `chain_deflate_le` | `Dinfty.SierpinskiApplication` |
| `D-0982` | def | `chaseDown` | `Dinfty.SierpinskiApplication` |
| `D-0983` | theorem | `chaseDown_mono` | `Dinfty.SierpinskiApplication` |
| `D-0984` | def | `chaseDownSet` | `Dinfty.SierpinskiApplication` |
| `D-0985` | theorem | `chaseDownSet_nonempty` | `Dinfty.SierpinskiApplication` |
| `D-0986` | theorem | `chaseDownSet_directed` | `Dinfty.SierpinskiApplication` |
| `D-0987` | def | `levelSup` | `Dinfty.SierpinskiApplication` |
| `D-0988` | theorem | `levelSup_compat` | `Dinfty.SierpinskiApplication` |
| `D-0989` | def | `applyEndPBilimit` | `Dinfty.SierpinskiApplication` |
| `D-0990` | theorem | `chaseDown_mono_in_y` | `Dinfty.SierpinskiApplication` |
| `D-0991` | theorem | `applyEndPBilimit_monotone` | `Dinfty.SierpinskiApplication` |
| `D-0992` | def | `ofEndPBilimit` | `Dinfty.SierpinskiApplication` |
| `D-0993` | theorem | `le_topSeq` | `Dinfty.SierpinskiApplication` |
| `D-0994` | theorem | `DBilimit_pLe_eq` | `Dinfty.SierpinskiApplication` |
| `D-0995` | theorem | `iotaD_ne_top` | `Dinfty.SierpinskiApplication` |
| `D-0996` | theorem | `insertAtLevel_topSeq_ne` | `Dinfty.SierpinskiApplication` |
| `D-0997` | def | `counterF` | `Dinfty.SierpinskiApplication` |
| `D-0998` | theorem | `counterF_topSeq` | `Dinfty.SierpinskiApplication` |
| `D-0999` | theorem | `counterF_approx` | `Dinfty.SierpinskiApplication` |
| `D-1000` | theorem | `toEndPBilimit_ofEndPBilimit_not_roundtrip` | `Dinfty.SierpinskiApplication` |
| `D-1001` | theorem | `iotaD_y_le` | `Dinfty.SierpinskiApplication` |
| `D-1002` | theorem | `iotaLe_y_le` | `Dinfty.SierpinskiApplication` |
| `D-1003` | theorem | `insertAtLevel_le_self` | `Dinfty.SierpinskiApplication` |
| `D-1004` | theorem | `insertAtLevel_chain_mono` | `Dinfty.SierpinskiApplication` |
| `D-1005` | def | `chainSet` | `Dinfty.SierpinskiApplication` |
| `D-1006` | theorem | `chainSet_nonempty` | `Dinfty.SierpinskiApplication` |
| `D-1007` | theorem | `chainSet_directedOn` | `Dinfty.SierpinskiApplication` |
| `D-1008` | theorem | `chainSet_isLUB` | `Dinfty.SierpinskiApplication` |
| `D-1009` | theorem | `toEndPBilimit_ofEndPBilimit_of_continuous` | `Dinfty.SierpinskiApplication` |
| `D-1010` | theorem | `insertAtLevel_self` | `Dinfty.SierpinskiApplication` |
| `D-1011` | theorem | `insertAtLevel_succ` | `Dinfty.SierpinskiApplication` |
| `D-1012` | theorem | `chaseDown_insertAtLevel_const` | `Dinfty.SierpinskiApplication` |
| `D-1013` | theorem | `toEndPBilimit_ofEndPBilimit` | `Dinfty.SierpinskiApplication` |
| `D-1014` | theorem | `_root_.IsLUB.dbilimit_apply` | `Dinfty.SierpinskiApplication` |
| `D-1015` | theorem | `applyEndPBilimit_scottContinuous` | `Dinfty.SierpinskiApplication` |
| `D-1016` | theorem | `toEndPBilimit_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1017` | theorem | `ofEndPBilimit_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1018` | instance | `inst-PartialOrder` | `Dinfty.SierpinskiApplication` |
| `D-1019` | def | `toEndPBilimitHom` | `Dinfty.SierpinskiApplication` |
| `D-1020` | def | `ofEndPBilimitHom` | `Dinfty.SierpinskiApplication` |
| `D-1021` | theorem | `toEndPBilimitHom_comp_ofEndPBilimitHom` | `Dinfty.SierpinskiApplication` |
| `D-1022` | theorem | `ofEndPBilimitHom_comp_toEndPBilimitHom` | `Dinfty.SierpinskiApplication` |
| `D-1023` | def | `endPBilimitOrderIso` | `Dinfty.SierpinskiApplication` |
| `D-1024` | def | `ShiftBilimit` | `Dinfty.SierpinskiApplication` |
| `D-1025` | instance | `inst-PartialOrder` | `Dinfty.SierpinskiApplication` |
| `D-1026` | def | `toShiftBilimit` | `Dinfty.SierpinskiApplication` |
| `D-1027` | def | `ofShiftBilimit` | `Dinfty.SierpinskiApplication` |
| `D-1028` | theorem | `toShiftBilimit_ofShiftBilimit` | `Dinfty.SierpinskiApplication` |
| `D-1029` | theorem | `ofShiftBilimit_toShiftBilimit` | `Dinfty.SierpinskiApplication` |
| `D-1030` | theorem | `toShiftBilimit_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1031` | theorem | `ofShiftBilimit_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1032` | def | `toShiftBilimitHom` | `Dinfty.SierpinskiApplication` |
| `D-1033` | def | `ofShiftBilimitHom` | `Dinfty.SierpinskiApplication` |
| `D-1034` | def | `dBilimitShiftIso` | `Dinfty.SierpinskiApplication` |
| `D-1035` | theorem | `glueA_pD_naive_square_fails` | `Dinfty.SierpinskiApplication` |
| `D-1036` | def | `liftEndP` | `Dinfty.SierpinskiApplication` |
| `D-1037` | theorem | `liftEndP_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1038` | theorem | `liftEndP_scottContinuous` | `Dinfty.SierpinskiApplication` |
| `D-1039` | theorem | `liftEndP_iotaEndP` | `Dinfty.SierpinskiApplication` |
| `D-1040` | theorem | `pD_bot` | `Dinfty.SierpinskiApplication` |
| `D-1041` | def | `botSeq` | `Dinfty.SierpinskiApplication` |
| `D-1042` | theorem | `botSeq_le` | `Dinfty.SierpinskiApplication` |
| `D-1043` | instance | `inst-OrderBot` | `Dinfty.SierpinskiApplication` |
| `D-1044` | theorem | `insertAtLevel_bot` | `Dinfty.SierpinskiApplication` |
| `D-1045` | instance | `inst-OrderTop` | `Dinfty.SierpinskiApplication` |
| `D-1046` | theorem | `scottContinuous_const` | `Dinfty.SierpinskiApplication` |
| `D-1047` | def | `scottEndPBot` | `Dinfty.SierpinskiApplication` |
| `D-1048` | def | `scottEndPTop` | `Dinfty.SierpinskiApplication` |
| `D-1049` | theorem | `scottEndPBot_le` | `Dinfty.SierpinskiApplication` |
| `D-1050` | theorem | `le_scottEndPTop` | `Dinfty.SierpinskiApplication` |
| `D-1051` | instance | `inst-OrderBot` | `Dinfty.SierpinskiApplication` |
| `D-1052` | instance | `inst-OrderTop` | `Dinfty.SierpinskiApplication` |
| `D-1053` | instance | `inst-BoundedOrder` | `Dinfty.SierpinskiApplication` |
| `D-1054` | theorem | `botSeq_ne_topSeq` | `Dinfty.SierpinskiApplication` |
| `D-1055` | def | `scottEndPId` | `Dinfty.SierpinskiApplication` |
| `D-1056` | theorem | `scottEndPId_apply` | `Dinfty.SierpinskiApplication` |
| `D-1057` | theorem | `scottEndPBot_apply` | `Dinfty.SierpinskiApplication` |
| `D-1058` | theorem | `scottEndPTop_apply` | `Dinfty.SierpinskiApplication` |
| `D-1059` | theorem | `scottEndPId_ne_bot` | `Dinfty.SierpinskiApplication` |
| `D-1060` | theorem | `scottEndPId_ne_top` | `Dinfty.SierpinskiApplication` |
| `D-1061` | theorem | `scottEndPBot_ne_top` | `Dinfty.SierpinskiApplication` |
| `D-1062` | def | `psiTargetOrder` | `Dinfty.SierpinskiApplication` |
| `D-1063` | def | `glueAA` | `Dinfty.SierpinskiApplication` |
| `D-1064` | theorem | `glueAA_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1065` | theorem | `glueAA_reflect` | `Dinfty.SierpinskiApplication` |
| `D-1066` | theorem | `glueAA_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-1067` | theorem | `glueAA_injective` | `Dinfty.SierpinskiApplication` |
| `D-1068` | theorem | `glueAA_iotaD` | `Dinfty.SierpinskiApplication` |
| `D-1069` | theorem | `pD_glueAA_deflation_tagA` | `Dinfty.SierpinskiApplication` |
| `D-1070` | theorem | `pD_glueAA_deflation_tagB` | `Dinfty.SierpinskiApplication` |
| `D-1071` | theorem | `pD_crossTag_CA_sufficient` | `Dinfty.SierpinskiApplication` |
| `D-1072` | def | `PsiInv` | `Dinfty.SierpinskiApplication` |
| `D-1073` | def | `liftEndPHom` | `Dinfty.SierpinskiApplication` |
| `D-1074` | theorem | `liftEndPHom_apply` | `Dinfty.SierpinskiApplication` |
| `D-1075` | theorem | `PsiInv_liftEndPHom` | `Dinfty.SierpinskiApplication` |
| `D-1076` | theorem | `PsiInv_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1077` | def | `constScottHom` | `Dinfty.SierpinskiApplication` |
| `D-1078` | theorem | `constScottHom_apply` | `Dinfty.SierpinskiApplication` |
| `D-1079` | theorem | `PsiInv_deflation` | `Dinfty.SierpinskiApplication` |
| `D-1080` | def | `Psi` | `Dinfty.SierpinskiApplication` |
| `D-1081` | theorem | `Psi_apply` | `Dinfty.SierpinskiApplication` |
| `D-1082` | theorem | `PsiInv_Psi` | `Dinfty.SierpinskiApplication` |
| `D-1083` | theorem | `Psi_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1084` | theorem | `Psi_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-1085` | theorem | `Psi_injective` | `Dinfty.SierpinskiApplication` |
| `D-1086` | theorem | `Psi_PsiInv_le` | `Dinfty.SierpinskiApplication` |
| `D-1087` | theorem | `pEndP_id` | `Dinfty.SierpinskiApplication` |
| `D-1088` | theorem | `pEndP_bot` | `Dinfty.SierpinskiApplication` |
| `D-1089` | theorem | `pEndP_top` | `Dinfty.SierpinskiApplication` |
| `D-1090` | def | `ebId` | `Dinfty.SierpinskiApplication` |
| `D-1091` | def | `ebBot` | `Dinfty.SierpinskiApplication` |
| `D-1092` | def | `ebTop` | `Dinfty.SierpinskiApplication` |
| `D-1093` | theorem | `ebBot_le` | `Dinfty.SierpinskiApplication` |
| `D-1094` | theorem | `le_ebTop` | `Dinfty.SierpinskiApplication` |
| `D-1095` | instance | `inst-OrderBot` | `Dinfty.SierpinskiApplication` |
| `D-1096` | instance | `inst-OrderTop` | `Dinfty.SierpinskiApplication` |
| `D-1097` | instance | `inst-BoundedOrder` | `Dinfty.SierpinskiApplication` |
| `D-1098` | theorem | `endPBilimitOrderIso_scottEndPId` | `Dinfty.SierpinskiApplication` |
| `D-1099` | def | `glueCarGenScottEndPId_iso_ebId` | `Dinfty.SierpinskiApplication` |
| `D-1100` | theorem | `DBilimit_reflexive` | `Dinfty.SierpinskiApplication` |
| `D-1101` | def | `eK` | `Dinfty.SierpinskiApplication` |
| `D-1102` | theorem | `eK_eq_insertAtLevel` | `Dinfty.SierpinskiApplication` |
| `D-1103` | theorem | `eK_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1104` | theorem | `eK_scottContinuous` | `Dinfty.SierpinskiApplication` |
| `D-1105` | def | `projK` | `Dinfty.SierpinskiApplication` |
| `D-1106` | theorem | `projK_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1107` | theorem | `projK_scottContinuous` | `Dinfty.SierpinskiApplication` |
| `D-1108` | theorem | `eK_projK_retraction` | `Dinfty.SierpinskiApplication` |
| `D-1109` | theorem | `eK_projK_deflation` | `Dinfty.SierpinskiApplication` |
| `D-1110` | structure | `IsColimitCocone` | `Dinfty.SierpinskiApplication` |
| `D-1111` | theorem | `DBilimit_isColimitCocone` | `Dinfty.SierpinskiApplication` |
| `D-1112` | instance | `instPartialOrderScottEndPD` | `Dinfty.SierpinskiApplication` |
| `D-1113` | def | `scottEndPBotD` | `Dinfty.SierpinskiApplication` |
| `D-1114` | def | `scottEndPTopD` | `Dinfty.SierpinskiApplication` |
| `D-1115` | theorem | `scottEndPBotD_le` | `Dinfty.SierpinskiApplication` |
| `D-1116` | theorem | `le_scottEndPTopD` | `Dinfty.SierpinskiApplication` |
| `D-1117` | instance | `instOrderBotScottEndPD` | `Dinfty.SierpinskiApplication` |
| `D-1118` | instance | `instOrderTopScottEndPD` | `Dinfty.SierpinskiApplication` |
| `D-1119` | instance | `instBoundedOrderScottEndPD` | `Dinfty.SierpinskiApplication` |
| `D-1120` | def | `endPScottEndPIso` | `Dinfty.SierpinskiApplication` |
| `D-1121` | example | `example-D` | `Dinfty.SierpinskiApplication` |
| `D-1122` | theorem | `fA_mapsTo_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-1123` | theorem | `fB_mapsTo_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-1124` | theorem | `fC_mapsTo_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-1125` | abbrev | `Addr` | `Dinfty.SierpinskiApplication` |
| `D-1126` | def | `symF` | `Dinfty.SierpinskiApplication` |
| `D-1127` | theorem | `lipschitzWith_symF` | `Dinfty.SierpinskiApplication` |
| `D-1128` | def | `wordPrefix` | `Dinfty.SierpinskiApplication` |
| `D-1129` | theorem | `wordPrefix_length` | `Dinfty.SierpinskiApplication` |
| `D-1130` | theorem | `wordPrefix_succ` | `Dinfty.SierpinskiApplication` |
| `D-1131` | def | `applyList` | `Dinfty.SierpinskiApplication` |
| `D-1132` | theorem | `applyList_nil` | `Dinfty.SierpinskiApplication` |
| `D-1133` | theorem | `applyList_cons` | `Dinfty.SierpinskiApplication` |
| `D-1134` | theorem | `lipschitzWith_applyList` | `Dinfty.SierpinskiApplication` |
| `D-1135` | theorem | `applyList_append_singleton` | `Dinfty.SierpinskiApplication` |
| `D-1136` | theorem | `applyList_mem_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-1137` | theorem | `fA_fixed_vA` | `Dinfty.SierpinskiApplication` |
| `D-1138` | theorem | `contractingWith_fA` | `Dinfty.SierpinskiApplication` |
| `D-1139` | theorem | `fixedPoint_fA_eq_vA` | `Dinfty.SierpinskiApplication` |
| `D-1140` | theorem | `fA_iterate_mem_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-1141` | theorem | `vA_mem_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-1142` | def | `piApprox` | `Dinfty.SierpinskiApplication` |
| `D-1143` | def | `piStepBound` | `Dinfty.SierpinskiApplication` |
| `D-1144` | theorem | `dist_symF_vA_le` | `Dinfty.SierpinskiApplication` |
| `D-1145` | theorem | `piApprox_succ_dist` | `Dinfty.SierpinskiApplication` |
| `D-1146` | theorem | `piApprox_cauchySeq` | `Dinfty.SierpinskiApplication` |
| `D-1147` | def | `piCoding` | `Dinfty.SierpinskiApplication` |
| `D-1148` | theorem | `piCoding_tendsto` | `Dinfty.SierpinskiApplication` |
| `D-1149` | theorem | `piCoding_mem_Gamma` | `Dinfty.SierpinskiApplication` |
| `D-1150` | def | `prependAddr` | `Dinfty.SierpinskiApplication` |
| `D-1151` | theorem | `wordPrefix_prepend` | `Dinfty.SierpinskiApplication` |
| `D-1152` | theorem | `piApprox_prepend_succ` | `Dinfty.SierpinskiApplication` |
| `D-1153` | theorem | `piCoding_equivariant` | `Dinfty.SierpinskiApplication` |
| `D-1154` | theorem | `constScottHom_bot_eq` | `Dinfty.SierpinskiApplication` |
| `D-1155` | theorem | `constScottHom_top_eq` | `Dinfty.SierpinskiApplication` |
| `D-1156` | theorem | `constScottHom_injective` | `Dinfty.SierpinskiApplication` |
| `D-1157` | theorem | `constScottHom_eq_bot_iff` | `Dinfty.SierpinskiApplication` |
| `D-1158` | theorem | `constScottHom_eq_top_iff` | `Dinfty.SierpinskiApplication` |
| `D-1159` | theorem | `constScottHom_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1160` | theorem | `leGlue_tagB_tagB_topGen` | `Dinfty.SierpinskiApplication` |
| `D-1161` | theorem | `tagC_one_le_tagB_top` | `Dinfty.SierpinskiApplication` |
| `D-1162` | theorem | `not_tagB_top_le_tagC_one` | `Dinfty.SierpinskiApplication` |
| `D-1163` | theorem | `tagC_cofinality_fails` | `Dinfty.SierpinskiApplication` |
| `D-1164` | theorem | `scottEndPId_ne_constScottHom` | `Dinfty.SierpinskiApplication` |
| `D-1165` | theorem | `Psi_isLUB` | `Dinfty.SierpinskiApplication` |
| `D-1166` | def | `topGen` | `Dinfty.SierpinskiApplication` |
| `D-1167` | theorem | `topGen_isTop` | `Dinfty.SierpinskiApplication` |
| `D-1168` | def | `topBGen` | `Dinfty.SierpinskiApplication` |
| `D-1169` | theorem | `topBGen_ne_topGen` | `Dinfty.SierpinskiApplication` |
| `D-1170` | def | `shiftAddr` | `Dinfty.SierpinskiApplication` |
| `D-1171` | theorem | `prependAddr_shiftAddr_eq` | `Dinfty.SierpinskiApplication` |
| `D-1172` | theorem | `topSeq_notMem_range_toDBilimit` | `Dinfty.SierpinskiApplication` |
| `D-1173` | def | `botGen` | `Dinfty.SierpinskiApplication` |
| `D-1174` | theorem | `botGen_isBot` | `Dinfty.SierpinskiApplication` |
| `D-1175` | theorem | `leGlueGen_tagC_tagB_top_iff` | `Dinfty.SierpinskiApplication` |
| `D-1176` | def | `PsiC` | `Dinfty.SierpinskiApplication` |
| `D-1177` | theorem | `PsiC_apply_of_ne_bot` | `Dinfty.SierpinskiApplication` |
| `D-1178` | theorem | `PsiC_apply_of_eq_bot` | `Dinfty.SierpinskiApplication` |
| `D-1179` | theorem | `exists_ne_bot_of_ne_bot_sup` | `Dinfty.SierpinskiApplication` |
| `D-1180` | theorem | `PsiC_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1181` | theorem | `PsiC_isLUB` | `Dinfty.SierpinskiApplication` |
| `D-1182` | theorem | `_root_.IsLUB.eq_topSeq_iff_forall_exists_top` | `Dinfty.SierpinskiApplication` |
| `D-1183` | theorem | `insertAtLevel_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1184` | theorem | `_root_.IsCompactElement.exists_insertAtLevel` | `Dinfty.SierpinskiApplication` |
| `D-1185` | theorem | `insertAtLevel_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-1186` | theorem | `DBilimit_compacts_le_directedOn` | `Dinfty.SierpinskiApplication` |
| `D-1187` | theorem | `DBilimit_isLUB_compacts_le` | `Dinfty.SierpinskiApplication` |
| `D-1188` | theorem | `toDBilimit_toD_eq_insertAtLevel` | `Dinfty.SierpinskiApplication` |
| `D-1189` | theorem | `mem_range_toDBilimit_iff_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1190` | theorem | `DBilimit_rigid_of_DInfty_rigid` | `Dinfty.SierpinskiApplication` |
| `D-1191` | theorem | `DBilimit_rigid_of_colimit_compat` | `Dinfty.SierpinskiApplication` |
| `D-1192` | def | `glue1Gen` | `Dinfty.SierpinskiApplication` |
| `D-1193` | def | `glue2Gen` | `Dinfty.SierpinskiApplication` |
| `D-1194` | def | `KEPT_A` | `Dinfty.SierpinskiApplication` |
| `D-1195` | def | `KEPT_C` | `Dinfty.SierpinskiApplication` |
| `D-1196` | def | `keptBGen` | `Dinfty.SierpinskiApplication` |
| `D-1197` | def | `Stage` | `Dinfty.SierpinskiApplication` |
| `D-1198` | theorem | `Stage_spec` | `Dinfty.SierpinskiApplication` |
| `D-1199` | theorem | `Stage_min` | `Dinfty.SierpinskiApplication` |
| `D-1200` | theorem | `Stage_transport` | `Dinfty.SierpinskiApplication` |
| `D-1201` | theorem | `canonGen_tagB_constScottHom_eq` | `Dinfty.SierpinskiApplication` |
| `D-1202` | theorem | `canonGen_tagC_constScottHom_eq` | `Dinfty.SierpinskiApplication` |
| `D-1203` | section | `§ Reconstructs `lemma_A3`'s 6-fact package (`lemma_A3_free`) — injectivity of each` | `Dinfty.SierpinskiApplication` |
| `D-1204` | theorem | `pD_glueA` | `Dinfty.SierpinskiApplication` |
| `D-1205` | def | `branchSeq` | `Dinfty.SierpinskiApplication` |
| `D-1206` | theorem | `branchSeq_ne_top` | `Dinfty.SierpinskiApplication` |
| `D-1207` | theorem | `branchSeq_succ_apply_bot` | `Dinfty.SierpinskiApplication` |
| `D-1208` | def | `branchPoint` | `Dinfty.SierpinskiApplication` |
| `D-1209` | theorem | `branchSeq_agree_of_agree` | `Dinfty.SierpinskiApplication` |
| `D-1210` | theorem | `branchSeq_succ_ne` | `Dinfty.SierpinskiApplication` |
| `D-1211` | theorem | `branchPoint_injective` | `Dinfty.SierpinskiApplication` |
| `D-1212` | theorem | `scottEndP_ext` | `Dinfty.SierpinskiApplication` |
| `D-1213` | theorem | `scottEndP_restrict_injective` | `Dinfty.SierpinskiApplication` |
| `D-1214` | theorem | `scottEndP_directed_image` | `Dinfty.SierpinskiApplication` |
| `D-1215` | def | `scottEndPSupFun` | `Dinfty.SierpinskiApplication` |
| `D-1216` | theorem | `scottEndPSupFun_isLUB` | `Dinfty.SierpinskiApplication` |
| `D-1217` | theorem | `scottEndPSupFun_monotone` | `Dinfty.SierpinskiApplication` |
| `D-1218` | theorem | `scottEndPSupFun_scottContinuous` | `Dinfty.SierpinskiApplication` |
| `D-1219` | def | `scottEndPSup` | `Dinfty.SierpinskiApplication` |
| `D-1220` | theorem | `scottEndPSup_isLUB` | `Dinfty.SierpinskiApplication` |
| `D-1221` | theorem | `ScottEndP.exists_isLUB_of_directedOn` | `Dinfty.SierpinskiApplication` |
| `D-1222` | theorem | `_root_.IsLUB.scottEndP_apply` | `Dinfty.SierpinskiApplication` |
| `D-1223` | theorem | `constScottHom_isCompactElement_of_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1224` | theorem | `topSeq_not_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1225` | theorem | `constScottHom_chainSet_topSeq_directedOn` | `Dinfty.SierpinskiApplication` |
| `D-1226` | theorem | `constScottHom_chainSet_topSeq_isLUB` | `Dinfty.SierpinskiApplication` |
| `D-1227` | theorem | `scottEndPTop_not_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1228` | def | `Gk` | `Dinfty.SierpinskiApplication` |
| `D-1229` | theorem | `Gk_apply` | `Dinfty.SierpinskiApplication` |
| `D-1230` | theorem | `Gk_mono_succ` | `Dinfty.SierpinskiApplication` |
| `D-1231` | theorem | `Gk_mono` | `Dinfty.SierpinskiApplication` |
| `D-1232` | theorem | `Gk_range_directedOn` | `Dinfty.SierpinskiApplication` |
| `D-1233` | theorem | `Gk_range_nonempty` | `Dinfty.SierpinskiApplication` |
| `D-1234` | theorem | `Gk_isLUB_scottEndPId` | `Dinfty.SierpinskiApplication` |
| `D-1235` | theorem | `Gk_not_ge_scottEndPId` | `Dinfty.SierpinskiApplication` |
| `D-1236` | theorem | `scottEndPId_not_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1237` | def | `tagBGenC` | `Dinfty.SierpinskiApplication` |
| `D-1238` | theorem | `Gk_ne_bot` | `Dinfty.SierpinskiApplication` |
| `D-1239` | theorem | `Gk_ne_scottEndPId` | `Dinfty.SierpinskiApplication` |
| `D-1240` | theorem | `tagCFam_directedOn` | `Dinfty.SierpinskiApplication` |
| `D-1241` | theorem | `tagCFam_isLUB_skelG3` | `Dinfty.SierpinskiApplication` |
| `D-1242` | theorem | `tagBGenC_not_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1243` | theorem | `tagBGenC_val` | `Dinfty.SierpinskiApplication` |
| `D-1244` | theorem | `chainSet_topSeq_constScottHom_ne_bot` | `Dinfty.SierpinskiApplication` |
| `D-1245` | theorem | `chainSet_topSeq_constScottHom_ne_top` | `Dinfty.SierpinskiApplication` |
| `D-1246` | theorem | `sigmaAFam_directedOn` | `Dinfty.SierpinskiApplication` |
| `D-1247` | theorem | `sigmaAFam_isLUB_skelG3` | `Dinfty.SierpinskiApplication` |
| `D-1248` | theorem | `Psi_not_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1249` | theorem | `DBilimit_injective_compactSetBelow` | `Dinfty.SierpinskiApplication` |
| `D-1250` | theorem | `compactSetBelow_eq_image` | `Dinfty.SierpinskiApplication` |
| `D-1251` | theorem | `DBilimit_injective_repsBelow` | `Dinfty.SierpinskiApplication` |
| `D-1252` | instance | `inst-Countable` | `Dinfty.SierpinskiApplication` |
| `D-1253` | theorem | `dbilimit_mk_eq_continuum` | `Dinfty.SierpinskiApplication` |
| `D-1254` | theorem | `mk_arrow_dbilimit_le` | `Dinfty.SierpinskiApplication` |
| `D-1255` | theorem | `scottEndP_dbilimit_mk_le` | `Dinfty.SierpinskiApplication` |
| `D-1256` | def | `scottEndP_to_dbilimit_inj` | `Dinfty.SierpinskiApplication` |
| `D-1257` | theorem | `glueCarGen_dbilimit_mk_le` | `Dinfty.SierpinskiApplication` |
| `D-1258` | def | `glueCarGen_to_dbilimit_inj` | `Dinfty.SierpinskiApplication` |
| `D-1259` | def | `rhoDF` | `Dinfty.SierpinskiApplication` |
| `D-1260` | theorem | `rhoDF_injective` | `Dinfty.SierpinskiApplication` |
| `D-1261` | instance | `inst-Nonempty` | `Dinfty.SierpinskiApplication` |
| `D-1262` | def | `psiDF` | `Dinfty.SierpinskiApplication` |
| `D-1263` | theorem | `psiDF_rhoDF` | `Dinfty.SierpinskiApplication` |
| `D-1264` | def | `sigmaA'` | `Dinfty.SierpinskiApplication` |
| `D-1265` | def | `sigmaB'` | `Dinfty.SierpinskiApplication` |
| `D-1266` | def | `sigmaC'` | `Dinfty.SierpinskiApplication` |
| `D-1267` | theorem | `sigmaA'_injective` | `Dinfty.SierpinskiApplication` |
| `D-1268` | theorem | `sigmaB'_injective` | `Dinfty.SierpinskiApplication` |
| `D-1269` | theorem | `sigmaC'_injective` | `Dinfty.SierpinskiApplication` |
| `D-1270` | theorem | `sigmaA'_ne_sigmaB'` | `Dinfty.SierpinskiApplication` |
| `D-1271` | theorem | `sigmaB'_ne_sigmaC'` | `Dinfty.SierpinskiApplication` |
| `D-1272` | theorem | `psi_topSeq_eq_tagC_botSeq` | `Dinfty.SierpinskiApplication` |
| `D-1273` | theorem | `sigmaC'_botSeq_eq_sigmaA'_topSeq` | `Dinfty.SierpinskiApplication` |
| `D-1274` | theorem | `sigmaA'_eq_sigmaC'_iff` | `Dinfty.SierpinskiApplication` |
| `D-1275` | theorem | `lemma_A3_free` | `Dinfty.SierpinskiApplication` |
| `D-1276` | theorem | `botSeq_isCompactElement` | `Dinfty.SierpinskiApplication` |
| `D-1277` | theorem | `prependAddr_constC` | `Dinfty.SierpinskiApplication` |
| `D-1278` | theorem | `constScottHom_isLUB` | `Dinfty.SierpinskiApplication` |
| `D-1279` | theorem | `leGlueGen_tagB_tagC_iff` | `Dinfty.SierpinskiApplication` |
| `D-1280` | theorem | `prependAddr_constB` | `Dinfty.SierpinskiApplication` |
| `D-1281` | def | `tagOf` | `Dinfty.SierpinskiApplication` |
| `D-1282` | theorem | `tagOf_glueOrderBot` | `Dinfty.SierpinskiApplication` |
| `D-1283` | theorem | `tagOf_glueOrderTop` | `Dinfty.SierpinskiApplication` |
| `D-1284` | theorem | `tagOf_bot` | `Dinfty.SierpinskiApplication` |
| `D-1285` | theorem | `tagOf_top` | `Dinfty.SierpinskiApplication` |
| `D-1286` | theorem | `interior_forces_tagA` | `Dinfty.SierpinskiApplication` |
| `D-1287` | theorem | `tagB_forces_prev_mid` | `Dinfty.SierpinskiApplication` |
| `D-1288` | theorem | `tagOf_ne_two_of_ne_top` | `Dinfty.SierpinskiApplication` |
| `D-1289` | theorem | `pD_dMid_succ` | `Dinfty.SierpinskiApplication` |
| `D-1290` | theorem | `tagOf_dMid_succ` | `Dinfty.SierpinskiApplication` |
| `D-1291` | theorem | `interior_gives_tagA` | `Dinfty.SierpinskiApplication` |
| `D-1292` | theorem | `interior_persists` | `Dinfty.SierpinskiApplication` |
| `D-1293` | theorem | `tag_stabilizes` | `Dinfty.SierpinskiApplication` |
| `D-1294` | theorem | `IsColimitCocone.proj_tower` | `Dinfty.SierpinskiApplication` |
| `D-1295` | theorem | `IsColimitCocone.proj_pLe` | `Dinfty.SierpinskiApplication` |
| `D-1296` | def | `IsColimitCocone.toDBil` | `Dinfty.SierpinskiApplication` |
| `D-1297` | theorem | `IsColimitCocone.toDBil_apply` | `Dinfty.SierpinskiApplication` |
| `D-1298` | theorem | `IsColimitCocone.toDBil_le_iff` | `Dinfty.SierpinskiApplication` |
| `D-1299` | theorem | `IsColimitCocone.toDBil_injective` | `Dinfty.SierpinskiApplication` |
| `D-1300` | theorem | `IsColimitCocone.toDBil_surjective` | `Dinfty.SierpinskiApplication` |
| `D-1301` | def | `IsColimitCocone.orderIsoDBil` | `Dinfty.SierpinskiApplication` |
| `D-1302` | theorem | `DBilimit_isColimitCocone_toDBil` | `Dinfty.SierpinskiApplication` |
| `D-1303` | def | `isColimitCocone_orderIso` | `Dinfty.SierpinskiApplication` |
| `D-1304` | section | `§ Obstruction (T) — the gluing tower's connecting map must preserve `⊤`` | `Dinfty.TripointedObstruction` |
| `D-1305` | theorem | `iota_top_of_topExact_natural` | `Dinfty.TripointedObstruction` |
| `D-1306` | theorem | `le_iota_top_of_monotone_of_idExact` | `Dinfty.TripointedObstruction` |
| `D-1307` | theorem | `no_topExact_natural_action_over_tower` | `Dinfty.TripointedObstruction` |
| `D-1308` | theorem | `no_monotone_idExact_natural_action_over_tower` | `Dinfty.TripointedObstruction` |
| `D-1309` | section | `§ Horn B: with a `⊥`/`⊤`-preserving tower map, conjugation is tripointed` | `Dinfty.HornBConjugation` |
| `D-1310` | def | `conj` | `Dinfty.HornBConjugation` |
| `D-1311` | theorem | `conj_apply` | `Dinfty.HornBConjugation` |
| `D-1312` | theorem | `conj_constHom` | `Dinfty.HornBConjugation` |
| `D-1313` | theorem | `conj_bot` | `Dinfty.HornBConjugation` |
| `D-1314` | theorem | `conj_top` | `Dinfty.HornBConjugation` |
| `D-1315` | theorem | `conj_monotone` | `Dinfty.HornBConjugation` |
| `D-1316` | theorem | `conj_le_reflect` | `Dinfty.HornBConjugation` |
| `D-1317` | theorem | `conj_sup` | `Dinfty.HornBConjugation` |
| `D-1318` | theorem | `conj_tripointed` | `Dinfty.HornBConjugation` |
| `D-1319` | theorem | `conj_id_eq_id_iff` | `Dinfty.HornBConjugation` |
| `D-1320` | section | `§ `Φ`'s morphism action under the `const_L` normalization` | `Dinfty.NormalizedGlueMap` |
| `D-1321` | def | `baseMap` | `Dinfty.NormalizedGlueMap` |
| `D-1322` | theorem | `map_eq_bot` | `Dinfty.NormalizedGlueMap` |
| `D-1323` | theorem | `map_eq_top` | `Dinfty.NormalizedGlueMap` |
| `D-1324` | theorem | `map_eq_mid` | `Dinfty.NormalizedGlueMap` |
| `D-1325` | theorem | `canon_baseMap` | `Dinfty.NormalizedGlueMap` |
| `D-1326` | theorem | `occs_baseMap` | `Dinfty.NormalizedGlueMap` |
| `D-1327` | theorem | `rawRule_baseMap` | `Dinfty.NormalizedGlueMap` |
| `D-1328` | theorem | `leGlue_baseMap` | `Dinfty.NormalizedGlueMap` |
| `D-1329` | def | `glueMap` | `Dinfty.NormalizedGlueMap` |
| `D-1330` | theorem | `glueMap_val` | `Dinfty.NormalizedGlueMap` |
| `D-1331` | theorem | `glueMap_monotone` | `Dinfty.NormalizedGlueMap` |
| `D-1332` | theorem | `glueMap_bot` | `Dinfty.NormalizedGlueMap` |
| `D-1333` | theorem | `glueMap_mid` | `Dinfty.NormalizedGlueMap` |
| `D-1334` | theorem | `glueA_self_eq_glue_aL_bT` | `Dinfty.NormalizedGlueMap` |
| `D-1335` | theorem | `glueMap_top` | `Dinfty.NormalizedGlueMap` |
| `D-1336` | theorem | `glueMap_midA` | `Dinfty.NormalizedGlueMap` |
| `D-1337` | section | `§ The normalized tower` | `Dinfty.NormalizedGlueMap` |
| `D-1338` | section | `§ Theorem B's up-transfer survives the normalization` | `Dinfty.NormalizedGlueMap` |
| `D-1339` | theorem | `id_not_le_constHom` | `Dinfty.NormalizedGlueMap` |
| `D-1340` | theorem | `constHom_not_le_id` | `Dinfty.NormalizedGlueMap` |
| `D-1341` | theorem | `tri_up_transfer` | `Dinfty.NormalizedGlueMap` |
| `D-1342` | theorem | `tri_level1_rigid` | `Dinfty.NormalizedGlueMap` |
| `D-1343` | section | `§ `D_down_transfer`'s inputs, normalized` | `Dinfty.NormalizedGlueMap` |
| `D-1344` | theorem | `constHom_ne_bot` | `Dinfty.NormalizedGlueMap` |
| `D-1345` | theorem | `constHom_ne_top` | `Dinfty.NormalizedGlueMap` |
| `D-1346` | theorem | `bot_ne_coatomOf_endP` | `Dinfty.NormalizedGlueMap` |
| `D-1347` | theorem | `coatomOf_endP_ne_constHom` | `Dinfty.NormalizedGlueMap` |
| `D-1348` | def | `tri_uniqueAtomCoatom` | `Dinfty.NormalizedGlueMap` |
| `D-1349` | theorem | `tri_J_connected` | `Dinfty.NormalizedGlueMap` |
| `D-1350` | theorem | `tri_has_interior_point` | `Dinfty.NormalizedGlueMap` |
| `D-1351` | section | `§ The two cover corollaries, landed` | `Dinfty.NormalizedGlueMap` |
| `D-1352` | theorem | `tri_top_hasUniqueDownCover` | `Dinfty.NormalizedGlueMap` |
| `D-1353` | theorem | `tri_bot_hasUniqueUpCover` | `Dinfty.NormalizedGlueMap` |
| `D-1354` | section | `§ `D_down_transfer` itself, level-parametric` | `Dinfty.NormalizedGlueMap` |
| `D-1355` | theorem | `general_down_transfer` | `Dinfty.NormalizedGlueMap` |
| `D-1356` | theorem | `general_down_transfer_recovers_D_down_transfer` | `Dinfty.NormalizedGlueMap` |
| `D-1357` | theorem | `tri_down_transfer` | `Dinfty.NormalizedGlueMap` |
| `D-1358` | structure | `TriLevel` | `Dinfty.NormalizedGlueMap` |
| `D-1359` | def | `triLevel0` | `Dinfty.NormalizedGlueMap` |
| `D-1360` | def | `markedPoint` | `Dinfty.NormalizedGlueMap` |
| `D-1361` | theorem | `markedPoint_ne_bot` | `Dinfty.NormalizedGlueMap` |
| `D-1362` | theorem | `markedPoint_ne_top` | `Dinfty.NormalizedGlueMap` |
| `D-1363` | def | `triLevelSucc` | `Dinfty.NormalizedGlueMap` |
| `D-1364` | def | `triLevel` | `Dinfty.NormalizedGlueMap` |
| `D-1365` | theorem | `triLevelSucc_mid_val` | `Dinfty.NormalizedGlueMap` |
| `D-1366` | section | `§ Local continuity of `Φ`'s morphism action` | `Dinfty.GlueMapContinuity` |
| `D-1367` | section | `§ 1. The morphism action is monotone in the morphism` | `Dinfty.GlueMapContinuity` |
| `D-1368` | theorem | `baseMap_leGlue_of_le` | `Dinfty.GlueMapContinuity` |
| `D-1369` | theorem | `glueMap_le_of_le` | `Dinfty.GlueMapContinuity` |
| `D-1370` | section | `§ 2. Directed families over a finite index attain their sup` | `Dinfty.GlueMapContinuity` |
| `D-1371` | theorem | `exists_greatest_of_directed` | `Dinfty.GlueMapContinuity` |
| `D-1372` | section | `§ 3. Local continuity at each finite level` | `Dinfty.GlueMapContinuity` |
| `D-1373` | theorem | `baseMap_directed_sup` | `Dinfty.GlueMapContinuity` |
| `D-1374` | theorem | `glueMap_directed_sup` | `Dinfty.GlueMapContinuity` |
| `D-1375` | section | `§ 4. The tower's levels are finite, so §3 applies at every level` | `Dinfty.GlueMapContinuity` |
| `D-1376` | instance | `triLevelFintype` | `Dinfty.GlueMapContinuity` |
| `D-1377` | section | `§ Local continuity in the infinite case — the reduction` | `Dinfty.GenContinuity` |
| `D-1378` | section | `§ The tagwise action, finiteness-free` | `Dinfty.GenContinuity` |
| `D-1379` | def | `baseMapGen` | `Dinfty.GenContinuity` |
| `D-1380` | theorem | `baseMapGen_inl` | `Dinfty.GenContinuity` |
| `D-1381` | theorem | `baseMapGen_leGlueGen_of_le` | `Dinfty.GenContinuity` |
| `D-1382` | section | `§ The reduction` | `Dinfty.GenContinuity` |
| `D-1383` | theorem | `baseMapGen_range_eq` | `Dinfty.GenContinuity` |
| `D-1384` | section | `§ The three obligations, named` | `Dinfty.GenContinuity` |
| `D-1385` | def | `ScottContinuousTagA` | `Dinfty.GenContinuity` |
| `D-1386` | section | `§ The gateway lemma for obligation 1` | `Dinfty.GenContinuity` |
| `D-1387` | theorem | `leGlueGen_tagA_tagA_iff` | `Dinfty.GenContinuity` |
| `D-1388` | theorem | `leGlueGen_tagA_tagC` | `Dinfty.GenContinuity` |
| `D-1389` | theorem | `le_marked_of_leGlueGen_tagB` | `Dinfty.GenContinuity` |
| `D-1390` | theorem | `tagAGen_isLUB` | `Dinfty.GenContinuity` |
| `D-1391` | theorem | `scottContinuousTagA` | `Dinfty.GenContinuity` |
| `D-1392` | section | `§ Obligations 2 and 3 — with a correction to how they were stated` | `Dinfty.GenContinuity` |
| `D-1393` | theorem | `occsGen_tagB` | `Dinfty.GenContinuity` |
| `D-1394` | theorem | `occsGen_tagC` | `Dinfty.GenContinuity` |
| `D-1395` | theorem | `leGlueGen_tagB_tagBtop` | `Dinfty.GenContinuity` |
| `D-1396` | theorem | `le_of_leGlueGen_tagB_tagB` | `Dinfty.GenContinuity` |
| `D-1397` | theorem | `marked_le_of_leGlueGen_tagB_tagC` | `Dinfty.GenContinuity` |
| `D-1398` | theorem | `tagB_isLUB_raw` | `Dinfty.GenContinuity` |
| `D-1399` | theorem | `tagC_isLUB_raw` | `Dinfty.GenContinuity` |
| `D-1400` | section | `§ Gap 1 of `GenContinuity`: transport of the copy-`B`/`C` obligations into` | `Dinfty.GenContinuityTransport` |
| `D-1401` | theorem | `occsGen_subset_canonGen` | `Dinfty.GenContinuityTransport` |
| `D-1402` | theorem | `leGlueGen_canonGen` | `Dinfty.GenContinuityTransport` |
| `D-1403` | def | `tagBGen` | `Dinfty.GenContinuityTransport` |
| `D-1404` | theorem | `tagBGen_val_of_ne_bot` | `Dinfty.GenContinuityTransport` |
| `D-1405` | theorem | `tagCGen_marked_eq_skelG3Gen` | `Dinfty.GenContinuityTransport` |
| `D-1406` | theorem | `tagBGen_isLUB` | `Dinfty.GenContinuityTransport` |
| `D-1407` | theorem | `tagCGen_isLUB` | `Dinfty.GenContinuityTransport` |
| `D-1408` | section | `§ Tags of a glued point, uniformly` | `Dinfty.GlueTag` |
| `D-1409` | section | `§ The tag as a number` | `Dinfty.GlueTag` |
| `D-1410` | def | `tagIdx` | `Dinfty.GlueTag` |
| `D-1411` | theorem | `tagIdx_le_two` | `Dinfty.GlueTag` |
| `D-1412` | theorem | `tagIdx_baseMapGen` | `Dinfty.GlueTag` |
| `D-1413` | theorem | `tagIdx_canonGen_le` | `Dinfty.GlueTag` |
| `D-1414` | section | `§ The tag-`t` inclusion` | `Dinfty.GlueTag` |
| `D-1415` | def | `tagInj` | `Dinfty.GlueTag` |
| `D-1416` | theorem | `tagInj_zero` | `Dinfty.GlueTag` |
| `D-1417` | theorem | `tagInj_one` | `Dinfty.GlueTag` |
| `D-1418` | theorem | `tagInj_two` | `Dinfty.GlueTag` |
| `D-1419` | theorem | `tagIdx_tagInj` | `Dinfty.GlueTag` |
| `D-1420` | theorem | `exists_payload` | `Dinfty.GlueTag` |
| `D-1421` | theorem | `baseMapGen_tagInj` | `Dinfty.GlueTag` |
| `D-1422` | section | `§ A left inverse, so each copy-inclusion is injective in one line` | `Dinfty.GlueTag` |
| `D-1423` | def | `unTag` | `Dinfty.GlueTag` |
| `D-1424` | theorem | `unTag_canonGen` | `Dinfty.GlueTag` |
| `D-1425` | theorem | `canonGen_tagInj_inj` | `Dinfty.GlueTag` |
| `D-1426` | section | `§ The bundled tag-`t` point, and its supremum law` | `Dinfty.GlueTag` |
| `D-1427` | def | `tagPt` | `Dinfty.GlueTag` |
| `D-1428` | theorem | `tagPt_val` | `Dinfty.GlueTag` |
| `D-1429` | theorem | `tagPt_injective` | `Dinfty.GlueTag` |
| `D-1430` | theorem | `tagPt_isLUB` | `Dinfty.GlueTag` |
| `D-1431` | section | `§ An order-reflecting, join-preserving map has an ep-partner` | `Dinfty.EpFromJoin` |
| `D-1432` | theorem | `monotone_of_sup` | `Dinfty.EpFromJoin` |
| `D-1433` | theorem | `map_finset_sup` | `Dinfty.EpFromJoin` |
| `D-1434` | def | `upper` | `Dinfty.EpFromJoin` |
| `D-1435` | theorem | `map_upper_le` | `Dinfty.EpFromJoin` |
| `D-1436` | theorem | `le_upper` | `Dinfty.EpFromJoin` |
| `D-1437` | theorem | `galoisConnection` | `Dinfty.EpFromJoin` |
| `D-1438` | theorem | `upper_monotone` | `Dinfty.EpFromJoin` |
| `D-1439` | theorem | `upper_map` | `Dinfty.EpFromJoin` |
| `D-1440` | theorem | `exists_epPartner` | `Dinfty.EpFromJoin` |
| `D-1441` | section | `§ Increasing unions of posets, and isomorphisms between them` | `Dinfty.ChainUnion` |
| `D-1442` | structure | `Pres` | `Dinfty.ChainUnion` |
| `D-1443` | theorem | `incl_injective` | `Dinfty.ChainUnion` |
| `D-1444` | def | `stepPow` | `Dinfty.ChainUnion` |
| `D-1445` | theorem | `incl_stepPow` | `Dinfty.ChainUnion` |
| `D-1446` | theorem | `stepPow_eq_of_incl_eq` | `Dinfty.ChainUnion` |
| `D-1447` | def | `Pres.dual` | `Dinfty.ChainUnion` |
| `D-1448` | def | `prodDualIso` | `Dinfty.ChainUnion` |
| `D-1449` | def | `dualDualIso` | `Dinfty.ChainUnion` |
| `D-1450` | section | `§ Transporting an isomorphism along two presentations` | `Dinfty.ChainUnion` |
| `D-1451` | theorem | `exists_common` | `Dinfty.ChainUnion` |
| `D-1452` | theorem | `e_stepPow` | `Dinfty.ChainUnion` |
| `D-1453` | theorem | `incl_e_eq` | `Dinfty.ChainUnion` |
| `D-1454` | def | `transfer` | `Dinfty.ChainUnion` |
| `D-1455` | theorem | `transfer_eq` | `Dinfty.ChainUnion` |
| `D-1456` | theorem | `hcomm_symm` | `Dinfty.ChainUnion` |
| `D-1457` | def | `chainUnionEquiv` | `Dinfty.ChainUnion` |
| `D-1458` | def | `chainUnionIso` | `Dinfty.ChainUnion` |
| `D-1459` | section | `§ No infinite absorption: `X ≇ X × 2` for the tower's restricted product` | `Dinfty.WeakProductAbsorption` |
| `D-1460` | section | `§ The atom-factor` | `Dinfty.WeakProductAbsorption` |
| `D-1461` | theorem | `orderIso_isAtom` | `Dinfty.WeakProductAbsorption` |
| `D-1462` | def | `atomFactor` | `Dinfty.WeakProductAbsorption` |
| `D-1463` | theorem | `bot_mem_atomFactor` | `Dinfty.WeakProductAbsorption` |
| `D-1464` | theorem | `mem_atomFactor_map` | `Dinfty.WeakProductAbsorption` |
| `D-1465` | section | `§ Two elements is two elements: the `× C₂` obstruction` | `Dinfty.WeakProductAbsorption` |
| `D-1466` | theorem | `isAtom_prodTop` | `Dinfty.WeakProductAbsorption` |
| `D-1467` | theorem | `atomFactor_prodTwo_top` | `Dinfty.WeakProductAbsorption` |
| `D-1468` | theorem | `no_iso_prod_two` | `Dinfty.WeakProductAbsorption` |
| `D-1469` | section | `§ The restricted product` | `Dinfty.WeakProductAbsorption` |
| `D-1470` | def | `WeakProd` | `Dinfty.WeakProductAbsorption` |
| `D-1471` | instance | `inst-PartialOrder` | `Dinfty.WeakProductAbsorption` |
| `D-1472` | theorem | `WeakProd.le_def` | `Dinfty.WeakProductAbsorption` |
| `D-1473` | instance | `inst-OrderBot` | `Dinfty.WeakProductAbsorption` |
| `D-1474` | theorem | `WeakProd.bot_apply` | `Dinfty.WeakProductAbsorption` |
| `D-1475` | theorem | `WeakProd.eq_bot_iff'` | `Dinfty.WeakProductAbsorption` |
| `D-1476` | def | `single` | `Dinfty.WeakProductAbsorption` |
| `D-1477` | theorem | `single_apply_self` | `Dinfty.WeakProductAbsorption` |
| `D-1478` | theorem | `single_apply_ne` | `Dinfty.WeakProductAbsorption` |
| `D-1479` | theorem | `single_le_iff` | `Dinfty.WeakProductAbsorption` |
| `D-1480` | section | `§ Atoms and atom-factors of the restricted product` | `Dinfty.WeakProductAbsorption` |
| `D-1481` | theorem | `isAtom_single` | `Dinfty.WeakProductAbsorption` |
| `D-1482` | theorem | `atom_eq_single` | `Dinfty.WeakProductAbsorption` |
| `D-1483` | theorem | `atomFactor_single` | `Dinfty.WeakProductAbsorption` |
| `D-1484` | theorem | `mem_atomFactor_single` | `Dinfty.WeakProductAbsorption` |
| `D-1485` | theorem | `isAtomic_weakProd` | `Dinfty.WeakProductAbsorption` |
| `D-1486` | theorem | `weakProd_no_absorb_two` | `Dinfty.WeakProductAbsorption` |
| `D-1487` | section | `§ Generation by atom-factors — the invariant that survives past level 1` | `Dinfty.AtomFactorGeneration` |
| `D-1488` | section | `§ The factor part, and generation` | `Dinfty.AtomFactorGeneration` |
| `D-1489` | def | `factorPart` | `Dinfty.AtomFactorGeneration` |
| `D-1490` | def | `GenByFactors` | `Dinfty.AtomFactorGeneration` |
| `D-1491` | section | `§ It is an order-theoretic property` | `Dinfty.AtomFactorGeneration` |
| `D-1492` | theorem | `mem_factorPart_map` | `Dinfty.AtomFactorGeneration` |
| `D-1493` | theorem | `factorPart_image` | `Dinfty.AtomFactorGeneration` |
| `D-1494` | theorem | `genByFactors_orderIso` | `Dinfty.AtomFactorGeneration` |
| `D-1495` | theorem | `no_iso_of_genByFactors_ne` | `Dinfty.AtomFactorGeneration` |
| `D-1496` | section | `§ The ordinal-sum obstruction, in the form that is actually used` | `Dinfty.AtomFactorGeneration` |
| `D-1497` | theorem | `not_genByFactors_of_strict_upper` | `Dinfty.AtomFactorGeneration` |
| `D-1498` | section | `§ Multiplicativity` | `Dinfty.AtomFactorGeneration` |
| `D-1499` | theorem | `prodIsAtom_iff` | `Dinfty.AtomFactorGeneration` |
| `D-1500` | theorem | `mem_factorPart_prod` | `Dinfty.AtomFactorGeneration` |
| `D-1501` | theorem | `genByFactors_prod_iff` | `Dinfty.AtomFactorGeneration` |
| `D-1502` | section | `§ The restricted product is generated by its atom-factors` | `Dinfty.AtomFactorGeneration` |
| `D-1503` | theorem | `single_mem_factorPart` | `Dinfty.AtomFactorGeneration` |
| `D-1504` | theorem | `genByFactors_weakProd` | `Dinfty.AtomFactorGeneration` |
| `D-1505` | theorem | `weakProd_prod_ne` | `Dinfty.AtomFactorGeneration` |
| `D-1506` | section | `§ The seed recursion, machine-checked` | `Dinfty.JSeedRecursion` |
| `D-1507` | section | `§ Two general facts` | `Dinfty.JSeedRecursion` |
| `D-1508` | def | `downSetIso` | `Dinfty.JSeedRecursion` |
| `D-1509` | def | `prodDownSetIso` | `Dinfty.JSeedRecursion` |
| `D-1510` | def | `prodCongrIso` | `Dinfty.JSeedRecursion` |
| `D-1511` | section | `§ The recursion` | `Dinfty.JSeedRecursion` |
| `D-1512` | def | `jSeedIso` | `Dinfty.JSeedRecursion` |
| `D-1513` | def | `downSet_toDual_bot` | `Dinfty.JSeedRecursion` |
| `D-1514` | def | `jSeedIso_bot` | `Dinfty.JSeedRecursion` |
| `D-1515` | theorem | `downSet_ne_univ_of_ne_bot` | `Dinfty.JSeedRecursion` |
| `D-1516` | section | `§ Gap 2 of `GenContinuity`: the mixed-variance (`End`) half` | `Dinfty.EndLocalContinuity` |
| `D-1517` | section | `§ The mixed-variance core` | `Dinfty.EndLocalContinuity` |
| `D-1518` | theorem | `comp_isLUB` | `Dinfty.EndLocalContinuity` |
| `D-1519` | theorem | `deflation_isLUB` | `Dinfty.EndLocalContinuity` |
| `D-1520` | section | `§ The variance fact itself, machine-checked` | `Dinfty.EndLocalContinuity` |
| `D-1521` | theorem | `ep_le_iff` | `Dinfty.EndLocalContinuity` |
| `D-1522` | section | `§ The bridge: pointwise suprema are hom-poset suprema` | `Dinfty.EndLocalContinuity` |
| `D-1523` | theorem | `isLUB_orderHom_of_pointwise` | `Dinfty.EndLocalContinuity` |
| `D-1524` | section | `§ The `End` action, bundled` | `Dinfty.EndLocalContinuity` |
| `D-1525` | def | `endHom` | `Dinfty.EndLocalContinuity` |
| `D-1526` | theorem | `endHom_apply` | `Dinfty.EndLocalContinuity` |
| `D-1527` | theorem | `endHom_isLUB` | `Dinfty.EndLocalContinuity` |
| `D-1528` | section | `§ The `Φ` half, in `GlueCarGen`, and the composite` | `Dinfty.EndLocalContinuity` |
| `D-1529` | theorem | `image_range_eq` | `Dinfty.EndLocalContinuity` |
| `D-1530` | theorem | `baseMapGen_isLUB_tagA` | `Dinfty.EndLocalContinuity` |
| `D-1531` | theorem | `baseMapGen_isLUB_tagB` | `Dinfty.EndLocalContinuity` |
| `D-1532` | theorem | `baseMapGen_isLUB_tagC` | `Dinfty.EndLocalContinuity` |
| `D-1533` | theorem | `phiEnd_isLUB_tagA` | `Dinfty.EndLocalContinuity` |
| `D-1534` | section | `§ How rigid is the `Gen`-layer morphism action?` | `Dinfty.BaseMapGenRigidity` |
| `D-1535` | section | `§ The positive half: copy-wise agreement characterises the action` | `Dinfty.BaseMapGenRigidity` |
| `D-1536` | theorem | `baseMapGen_unique` | `Dinfty.BaseMapGenRigidity` |
| `D-1537` | section | `§ The negative half: copy `A` (and even copy `C`) is not enough` | `Dinfty.BaseMapGenRigidity` |
| `D-1538` | def | `collapseB` | `Dinfty.BaseMapGenRigidity` |
| `D-1539` | theorem | `collapseB_inl` | `Dinfty.BaseMapGenRigidity` |
| `D-1540` | theorem | `collapseB_inr_inr` | `Dinfty.BaseMapGenRigidity` |
| `D-1541` | theorem | `collapseB_eq_on_tagA` | `Dinfty.BaseMapGenRigidity` |
| `D-1542` | theorem | `collapseB_eq_on_tagC` | `Dinfty.BaseMapGenRigidity` |
| `D-1543` | theorem | `collapseB_canonGen_fixed` | `Dinfty.BaseMapGenRigidity` |
| `D-1544` | theorem | `collapseB_monotone` | `Dinfty.BaseMapGenRigidity` |
| `D-1545` | theorem | `collapseB_ne_baseMapGen` | `Dinfty.BaseMapGenRigidity` |
| `D-1546` | section | `§ The copy-`B` component is unconstrained — and the freedom is not a collapse` | `Dinfty.CopyBFreedom` |
| `D-1547` | def | `glueTwist` | `Dinfty.CopyBFreedom` |
| `D-1548` | theorem | `glueTwist_inl` | `Dinfty.CopyBFreedom` |
| `D-1549` | theorem | `glueTwist_inr_inl` | `Dinfty.CopyBFreedom` |
| `D-1550` | theorem | `glueTwist_inr_inr` | `Dinfty.CopyBFreedom` |
| `D-1551` | theorem | `glueTwist_eq_on_tagA` | `Dinfty.CopyBFreedom` |
| `D-1552` | theorem | `glueTwist_eq_on_tagC` | `Dinfty.CopyBFreedom` |
| `D-1553` | theorem | `glueTwist_canonGen_fixed` | `Dinfty.CopyBFreedom` |
| `D-1554` | theorem | `glueTwist_monotone` | `Dinfty.CopyBFreedom` |
| `D-1555` | theorem | `glueTwist_injective` | `Dinfty.CopyBFreedom` |
| `D-1556` | theorem | `glueTwist_ne_baseMapGen` | `Dinfty.CopyBFreedom` |
| `D-1557` | section | `§ A concrete injective witness: the diamond, twisted by `Prod.swap`` | `Dinfty.CopyBFreedom` |
| `D-1558` | def | `swapHom` | `Dinfty.CopyBFreedom` |
| `D-1559` | theorem | `swapHom_apply` | `Dinfty.CopyBFreedom` |
| `D-1560` | theorem | `swapHom_injective` | `Dinfty.CopyBFreedom` |
| `D-1561` | theorem | `swapHom_top` | `Dinfty.CopyBFreedom` |
| `D-1562` | theorem | `swapHom_ne_bot` | `Dinfty.CopyBFreedom` |
| `D-1563` | theorem | `swapTwist_ne_baseMapGen` | `Dinfty.CopyBFreedom` |
| `D-1564` | theorem | `swapTwist_injective` | `Dinfty.CopyBFreedom` |
| `D-1565` | section | `§ On a finite poset, a monotone injection is an order isomorphism — and on a` | `Dinfty.MonotoneInjectionRigid` |
| `D-1566` | theorem | `le_of_apply_le` | `Dinfty.MonotoneInjectionRigid` |
| `D-1567` | def | `orderIsoOfMonotoneInjective` | `Dinfty.MonotoneInjectionRigid` |
| `D-1568` | theorem | `orderIsoOfMonotoneInjective_apply` | `Dinfty.MonotoneInjectionRigid` |
| `D-1569` | theorem | `eq_id_of_rigid` | `Dinfty.MonotoneInjectionRigid` |
| `D-1570` | section | `§ The consequence for `glueTwist`` | `Dinfty.MonotoneInjectionRigid` |
| `D-1571` | theorem | `glueTwist_eq_baseMapGen_of_rigid` | `Dinfty.MonotoneInjectionRigid` |
| `D-1572` | theorem | `twist_trivial_of_rigid` | `Dinfty.MonotoneInjectionRigid` |
| `D-1573` | section | `§ The free consequence at the tower: `D_all_rigid` upgrades to` | `Dinfty.MonotoneInjectionRigid` |
| `D-1574` | theorem | `D_monotone_injection_eq_id` | `Dinfty.MonotoneInjectionRigid` |
| `D-1575` | theorem | `D_orderHom_injection_eq_id` | `Dinfty.MonotoneInjectionRigid` |
| `D-1576` | section | `§ Level-stability of join-irreducibility — clause (3b) of the join-recoverability` | `Dinfty.JoinIrredLevelStable` |
| `D-1577` | theorem | `joinIrred_iotaD_iff` | `Dinfty.JoinIrredLevelStable` |
| `D-1578` | theorem | `joinIrred_iotaLe_iff` | `Dinfty.JoinIrredLevelStable` |
| `D-1579` | theorem | `not_joinIrred_iotaLe` | `Dinfty.JoinIrredLevelStable` |
| `D-1580` | section | `§ What remains for (3b) as stated in §9.2` | `Dinfty.JoinIrredLevelStable` |
| `D-1581` | section | `§ The seed's level step, at the tower` | `Dinfty.SeedLevelStep` |
| `D-1582` | section | `§ `constHom` is the step map at threshold `⊥`` | `Dinfty.SeedLevelStep` |
| `D-1583` | theorem | `stepMap_bot` | `Dinfty.SeedLevelStep` |
| `D-1584` | theorem | `jiOrderIso_bot_val` | `Dinfty.SeedLevelStep` |
| `D-1585` | section | `§ The seed at a level` | `Dinfty.SeedLevelStep` |
| `D-1586` | abbrev | `LevelSeed` | `Dinfty.SeedLevelStep` |
| `D-1587` | def | `subtypeShuffle` | `Dinfty.SeedLevelStep` |
| `D-1588` | section | `§ Copy `A` carries the seed up a level` | `Dinfty.SeedLevelStep` |
| `D-1589` | theorem | `hm_k` | `Dinfty.SeedLevelStep` |
| `D-1590` | theorem | `hmt_k` | `Dinfty.SeedLevelStep` |
| `D-1591` | theorem | `hbt_k` | `Dinfty.SeedLevelStep` |
| `D-1592` | abbrev | `jiBot` | `Dinfty.SeedLevelStep` |
| `D-1593` | def | `copyAFun` | `Dinfty.SeedLevelStep` |
| `D-1594` | theorem | `copyAFun_injective` | `Dinfty.SeedLevelStep` |
| `D-1595` | theorem | `copyAFun_surjective` | `Dinfty.SeedLevelStep` |
| `D-1596` | def | `copyAIso` | `Dinfty.SeedLevelStep` |
| `D-1597` | theorem | `copyAIso_apply` | `Dinfty.SeedLevelStep` |
| `D-1598` | section | `§ The level step` | `Dinfty.SeedLevelStep` |
| `D-1599` | def | `levelStepIso` | `Dinfty.SeedLevelStep` |
| `D-1600` | section | `§ …and the tower's own embedding is the `⊥`-insertion` | `Dinfty.SeedLevelStep` |
| `D-1601` | theorem | `levelStepIso_symm_bot` | `Dinfty.SeedLevelStep` |
| `D-1602` | section | `§ Assembly scaffold: the pillars' reductions, compiled rather than narrated` | `Dinfty.Assembly` |
| `D-1603` | def | `StageDefinable` | `Dinfty.Assembly` |
| `D-1604` | theorem | `toD_inj` | `Dinfty.Assembly` |
| `D-1605` | theorem | `eq_refl_of_stageDefinable` | `Dinfty.Assembly` |
| `D-1606` | theorem | `colimit_rigid_of_stageDefinable` | `Dinfty.Assembly` |
| `D-1607` | theorem | `DBilimit_rigid_of_stageDefinable` | `Dinfty.Assembly` |
| `D-1608` | section | `§ The rest of pillar B's chain, compiled` | `Dinfty.AssemblyChain` |
| `D-1609` | def | `JoinIrredStagePreserved` | `Dinfty.AssemblyChain` |
| `D-1610` | def | `StageJoinRecoverable` | `Dinfty.AssemblyChain` |
| `D-1611` | def | `StageSupClosed` | `Dinfty.AssemblyChain` |
| `D-1612` | theorem | `stageDefinable_of` | `Dinfty.AssemblyChain` |
| `D-1613` | theorem | `DBilimit_rigid_of_chain` | `Dinfty.AssemblyChain` |
| `D-1614` | section | `§ Piping `colimit_compat`: two of the three open `Prop`s discharged` | `Dinfty.ColimitCompatPipe` |
| `D-1615` | section | `§ `toD k ⊥` is a least element of `DInfty`` | `Dinfty.ColimitCompatPipe` |
| `D-1616` | theorem | `iotaD_bot` | `Dinfty.ColimitCompatPipe` |
| `D-1617` | theorem | `iotaLe_bot` | `Dinfty.ColimitCompatPipe` |
| `D-1618` | theorem | `toD_bot_le` | `Dinfty.ColimitCompatPipe` |
| `D-1619` | section | `§ `toD k` preserves finite joins` | `Dinfty.ColimitCompatPipe` |
| `D-1620` | theorem | `toD_sup_le` | `Dinfty.ColimitCompatPipe` |
| `D-1621` | section | `§ The two `Prop`s` | `Dinfty.ColimitCompatPipe` |
| `D-1622` | theorem | `stageJoinRecoverable` | `Dinfty.ColimitCompatPipe` |
| `D-1623` | theorem | `stageSupClosed` | `Dinfty.ColimitCompatPipe` |
| `D-1624` | theorem | `stage_finite` | `Dinfty.ColimitCompatPipe` |
| `D-1625` | section | `§ The chain, with one link left` | `Dinfty.ColimitCompatPipe` |
| `D-1626` | theorem | `colimit_rigid_of_joinIrredStagePreserved` | `Dinfty.ColimitCompatPipe` |
| `D-1627` | theorem | `DBilimit_rigid_of_joinIrredStagePreserved` | `Dinfty.ColimitCompatPipe` |
| `D-1628` | theorem | `colimit_compat_of_joinIrredStagePreserved` | `Dinfty.ColimitCompatPipe` |
| `D-1629` | theorem | `DBilimit_rigid_of_joinIrredStagePreserved'` | `Dinfty.ColimitCompatPipe` |
| `D-1630` | section | `§ The `DInfty`-level half of clause (3b), and the residue with no join-irreducibility left in it` | `Dinfty.JoinIrredDInfty` |
| `D-1631` | instance | `inst-OrderBot` | `Dinfty.JoinIrredDInfty` |
| `D-1632` | theorem | `bot_eq_toD` | `Dinfty.JoinIrredDInfty` |
| `D-1633` | theorem | `toD_eq_bot_iff` | `Dinfty.JoinIrredDInfty` |
| `D-1634` | section | `§ Order isomorphisms preserve join-irreducibility` | `Dinfty.JoinIrredDInfty` |
| `D-1635` | section | `§ The `DInfty`-level characterization` | `Dinfty.JoinIrredDInfty` |
| `D-1636` | theorem | `joinIrred_toD_iff` | `Dinfty.JoinIrredDInfty` |
| `D-1637` | section | `§ The residue, with the join-irreducibility bookkeeping removed` | `Dinfty.JoinIrredDInfty` |
| `D-1638` | def | `StageFixed` | `Dinfty.JoinIrredDInfty` |
| `D-1639` | theorem | `joinIrredStagePreserved_of_stageFixed` | `Dinfty.JoinIrredDInfty` |
| `D-1640` | section | `§ `colimit_compat` from the tightened residue` | `Dinfty.JoinIrredDInfty` |
| `D-1641` | theorem | `colimit_rigid_of_stageFixed` | `Dinfty.JoinIrredDInfty` |
| `D-1642` | theorem | `colimit_compat_of_stageFixed` | `Dinfty.JoinIrredDInfty` |
| `D-1643` | theorem | `DBilimit_rigid_of_stageFixed` | `Dinfty.JoinIrredDInfty` |
| `D-1644` | section | `§ "Distance to `D_0`" has no foothold at either end of `DInfty`` | `Dinfty.DInftyNoFootholds` |
| `D-1645` | section | `§ The spike` | `Dinfty.DInftyNoFootholds` |
| `D-1646` | def | `spike` | `Dinfty.DInftyNoFootholds` |
| `D-1647` | theorem | `spike_apply_top` | `Dinfty.DInftyNoFootholds` |
| `D-1648` | theorem | `spike_apply_bot` | `Dinfty.DInftyNoFootholds` |
| `D-1649` | theorem | `spike_le_constHom` | `Dinfty.DInftyNoFootholds` |
| `D-1650` | theorem | `spike_ne_bot` | `Dinfty.DInftyNoFootholds` |
| `D-1651` | theorem | `spike_ne_constHom` | `Dinfty.DInftyNoFootholds` |
| `D-1652` | section | `§ Atomlessness` | `Dinfty.DInftyNoFootholds` |
| `D-1653` | theorem | `exists_lt_lt_of_ne_bot` | `Dinfty.DInftyNoFootholds` |
| `D-1654` | theorem | `no_isAtom` | `Dinfty.DInftyNoFootholds` |
| `D-1655` | section | `§ No top` | `Dinfty.DInftyNoFootholds` |
| `D-1656` | theorem | `no_top` | `Dinfty.DInftyNoFootholds` |
| `D-1657` | theorem | `no_footholds` | `Dinfty.DInftyNoFootholds` |
| `D-1658` | section | `§ Where they cancel: the seam, and a canonical anchor at neither `⊥` nor `⊤`` | `Dinfty.MidAnchor` |
| `D-1659` | section | `§ The marked points are colimit-coherent` | `Dinfty.MidAnchor` |
| `D-1660` | theorem | `dMid_succ_eq_iotaD` | `Dinfty.MidAnchor` |
| `D-1661` | theorem | `iotaLe_dMid` | `Dinfty.MidAnchor` |
| `D-1662` | def | `midInf` | `Dinfty.MidAnchor` |
| `D-1663` | theorem | `toD_dMid` | `Dinfty.MidAnchor` |
| `D-1664` | section | `§ `midInf` is interior on both sides` | `Dinfty.MidAnchor` |
| `D-1665` | theorem | `midInf_ne_bot` | `Dinfty.MidAnchor` |
| `D-1666` | theorem | `bot_lt_midInf` | `Dinfty.MidAnchor` |
| `D-1667` | theorem | `midInf_lt_toD_top` | `Dinfty.MidAnchor` |
| `D-1668` | section | `§ An automorphism that maps a stage into itself is the identity there` | `Dinfty.MidAnchor` |
| `D-1669` | theorem | `fixes_stage_of_maps_into` | `Dinfty.MidAnchor` |
| `D-1670` | theorem | `fixes_midInf_of_maps_into` | `Dinfty.MidAnchor` |
| `D-1671` | theorem | `fixes_toD_zero_top_of_maps_into` | `Dinfty.MidAnchor` |
| `D-1672` | theorem | `stage_zero_eq` | `Dinfty.MidAnchor` |
| `D-1673` | section | `§ The two-point hypothesis` | `Dinfty.TwoPointHypothesis` |
| `D-1674` | section | `§ The two `Prop`s` | `Dinfty.TwoPointHypothesis` |
| `D-1675` | def | `StageFixedZero` | `Dinfty.TwoPointHypothesis` |
| `D-1676` | def | `TwoPointFixed` | `Dinfty.TwoPointHypothesis` |
| `D-1677` | section | `§ The equivalence` | `Dinfty.TwoPointHypothesis` |
| `D-1678` | theorem | `orderIso_map_bot` | `Dinfty.TwoPointHypothesis` |
| `D-1679` | theorem | `stageFixedZero_iff_twoPointFixed` | `Dinfty.TwoPointHypothesis` |
| `D-1680` | section | `§ Necessity — so the hypothesis is falsifiable` | `Dinfty.TwoPointHypothesis` |
| `D-1681` | theorem | `joinIrred_D0_top` | `Dinfty.TwoPointHypothesis` |
| `D-1682` | theorem | `stageFixed_imp_stageFixedZero` | `Dinfty.TwoPointHypothesis` |
| `D-1683` | theorem | `stageFixed_imp_twoPointFixed` | `Dinfty.TwoPointHypothesis` |
| `D-1684` | theorem | `not_stageFixed_of_not_twoPointFixed` | `Dinfty.TwoPointHypothesis` |
| `D-1685` | section | `§ Both points are join-irreducible in the colimit` | `Dinfty.TwoPointHypothesis` |
| `D-1686` | theorem | `joinIrred_midInf` | `Dinfty.TwoPointHypothesis` |
| `D-1687` | theorem | `joinIrred_toD_zero_top` | `Dinfty.TwoPointHypothesis` |
| `D-1688` | theorem | `midInf_lt_top_zero` | `Dinfty.TwoPointHypothesis` |
| `D-1689` | section | `§ Attacking `TwoPointFixed`: reduce to the join-irreducible poset `J∞`` | `Dinfty.JinfReduction` |
| `D-1690` | section | `§ The join-irreducible poset` | `Dinfty.JinfReduction` |
| `D-1691` | def | `Jinf` | `Dinfty.JinfReduction` |
| `D-1692` | instance | `inst-PartialOrder` | `Dinfty.JinfReduction` |
| `D-1693` | theorem | `Jinf_le_iff` | `Dinfty.JinfReduction` |
| `D-1694` | def | `Jmap` | `Dinfty.JinfReduction` |
| `D-1695` | theorem | `Jmap_val` | `Dinfty.JinfReduction` |
| `D-1696` | section | `§ `J∞` is the increasing union of the finite `J(D k)`` | `Dinfty.JinfReduction` |
| `D-1697` | theorem | `jinf_exists_stage` | `Dinfty.JinfReduction` |
| `D-1698` | theorem | `mem_jinf_of_stage` | `Dinfty.JinfReduction` |
| `D-1699` | theorem | `stage_jinf_finite` | `Dinfty.JinfReduction` |
| `D-1700` | section | `§ The two points, and the transported hypothesis` | `Dinfty.JinfReduction` |
| `D-1701` | def | `midJ` | `Dinfty.JinfReduction` |
| `D-1702` | def | `topJ` | `Dinfty.JinfReduction` |
| `D-1703` | theorem | `midJ_lt_topJ` | `Dinfty.JinfReduction` |
| `D-1704` | theorem | `twoPointFixed_iff_jinf` | `Dinfty.JinfReduction` |
| `D-1705` | theorem | `not_stageFixed_of_jinf_moves` | `Dinfty.JinfReduction` |
| `D-1706` | section | `§ The two points differ only in a seed` | `Dinfty.SeedContrast` |
| `D-1707` | theorem | `endP_le_constHom_iff` | `Dinfty.SeedContrast` |
| `D-1708` | theorem | `stepMap_le_constHom_iff` | `Dinfty.SeedContrast` |
| `D-1709` | theorem | `jiEndP_below_constHom` | `Dinfty.SeedContrast` |
| `D-1710` | theorem | `stepMap_param_inj` | `Dinfty.SeedContrast` |
| `D-1711` | theorem | `jiEndP_below_constHom_congr` | `Dinfty.SeedContrast` |
| `D-1712` | section | `§ The two seeds, at level `0`` | `Dinfty.SeedContrast` |
| `D-1713` | theorem | `joinIrred_fin3_iff` | `Dinfty.SeedContrast` |
| `D-1714` | theorem | `seed_mid` | `Dinfty.SeedContrast` |
| `D-1715` | theorem | `seed_top` | `Dinfty.SeedContrast` |
| `D-1716` | theorem | `seeds_differ` | `Dinfty.SeedContrast` |
| `D-1717` | section | `§ Stop iterating: solve the recursion at the level of its factors` | `Dinfty.Indecomposable` |
| `D-1718` | section | `§ The fixed-point obstruction` | `Dinfty.Indecomposable` |
| `D-1719` | theorem | `not_iso_prod_of_least_nonbot` | `Dinfty.Indecomposable` |
| `D-1720` | def | `DirectlyIndecomposable` | `Dinfty.Indecomposable` |
| `D-1721` | theorem | `directlyIndecomposable_of_least_nonbot` | `Dinfty.Indecomposable` |
| `D-1722` | section | `§ Every level of the tower` | `Dinfty.Indecomposable` |
| `D-1723` | theorem | `D_directlyIndecomposable` | `Dinfty.Indecomposable` |
| `D-1724` | theorem | `D_card_ne_two` | `Dinfty.Indecomposable` |
| `D-1725` | section | `§ The residue is a *definability* statement — and that is why the reductions circle` | `Dinfty.Definability` |
| `D-1726` | def | `OrderInvariant` | `Dinfty.Definability` |
| `D-1727` | def | `Pins` | `Dinfty.Definability` |
| `D-1728` | theorem | `invariant_pin_iff_fixed` | `Dinfty.Definability` |
| `D-1729` | theorem | `eq_pin_invariant_iff` | `Dinfty.Definability` |
| `D-1730` | theorem | `twoPointFixed_iff_pinned` | `Dinfty.Definability` |
| `D-1731` | theorem | `completeness_dichotomy` | `Dinfty.Definability` |
| `D-1732` | section | `§ The search, written into Lean` | `Dinfty.SeedSeparation` |
| `D-1733` | section | `§ The seed, in colimit form` | `Dinfty.SeedSeparation` |
| `D-1734` | def | `JBelow` | `Dinfty.SeedSeparation` |
| `D-1735` | instance | `inst-DInfty` | `Dinfty.SeedSeparation` |
| `D-1736` | def | `JBelow.map` | `Dinfty.SeedSeparation` |
| `D-1737` | section | `§ Every element lies in a stage` | `Dinfty.SeedSeparation` |
| `D-1738` | theorem | `exists_stage` | `Dinfty.SeedSeparation` |
| `D-1739` | section | `§ The hypothesis the search instantiates` | `Dinfty.SeedSeparation` |
| `D-1740` | def | `SeedSeparatesAt` | `Dinfty.SeedSeparation` |
| `D-1741` | theorem | `fixed_of_seedSeparates` | `Dinfty.SeedSeparation` |
| `D-1742` | theorem | `twoPointFixed_of_seedSeparates` | `Dinfty.SeedSeparation` |
| `D-1743` | section | `§ The part of the search Lean can replay: the `⊥` exclusion` | `Dinfty.SeedSeparation` |
| `D-1744` | theorem | `jBelow_bot_isEmpty` | `Dinfty.SeedSeparation` |
| `D-1745` | theorem | `jBelow_nonempty_of_joinIrred` | `Dinfty.SeedSeparation` |
| `D-1746` | theorem | `bot_ne_of_seed_iso` | `Dinfty.SeedSeparation` |
| `D-1747` | theorem | `bot_ne_midInf_seed` | `Dinfty.SeedSeparation` |
| `D-1748` | theorem | `bot_ne_topJ_seed` | `Dinfty.SeedSeparation` |
| `D-1749` | section | `§ `JBelow z` is the increasing union of the level-wise seeds` | `Dinfty.SeedChain` |
| `D-1750` | def | `yAt` | `Dinfty.SeedChain` |
| `D-1751` | theorem | `yAt_zero` | `Dinfty.SeedChain` |
| `D-1752` | theorem | `yAt_succ` | `Dinfty.SeedChain` |
| `D-1753` | theorem | `toD_yAt` | `Dinfty.SeedChain` |
| `D-1754` | theorem | `joinIrred_yAt` | `Dinfty.SeedChain` |
| `D-1755` | section | `§ The chain` | `Dinfty.SeedChain` |
| `D-1756` | abbrev | `SeedAt` | `Dinfty.SeedChain` |
| `D-1757` | def | `seedStep` | `Dinfty.SeedChain` |
| `D-1758` | def | `seedIncl` | `Dinfty.SeedChain` |
| `D-1759` | theorem | `seedIncl_le_iff` | `Dinfty.SeedChain` |
| `D-1760` | theorem | `seedIncl_step` | `Dinfty.SeedChain` |
| `D-1761` | theorem | `seedIncl_surj` | `Dinfty.SeedChain` |
| `D-1762` | def | `jBelowPres` | `Dinfty.SeedChain` |
| `D-1763` | section | `§ Unique factorization for restricted products` | `Dinfty.WeakProdFactorization` |
| `D-1764` | section | `§ Atom-factors correspond along an isomorphism` | `Dinfty.WeakProdFactorization` |
| `D-1765` | def | `atomFactorIso` | `Dinfty.WeakProdFactorization` |
| `D-1766` | section | `§ The axes of a restricted product` | `Dinfty.WeakProdFactorization` |
| `D-1767` | theorem | `single_lam_inj` | `Dinfty.WeakProdFactorization` |
| `D-1768` | theorem | `eq_single_of_mem_atomFactor` | `Dinfty.WeakProdFactorization` |
| `D-1769` | def | `axisIso` | `Dinfty.WeakProdFactorization` |
| `D-1770` | section | `§ The induced permutation of factors` | `Dinfty.WeakProdFactorization` |
| `D-1771` | theorem | `exists_transfer` | `Dinfty.WeakProdFactorization` |
| `D-1772` | def | `transferIndex` | `Dinfty.WeakProdFactorization` |
| `D-1773` | theorem | `transferIndex_eq` | `Dinfty.WeakProdFactorization` |
| `D-1774` | theorem | `transferIndex_spec` | `Dinfty.WeakProdFactorization` |
| `D-1775` | theorem | `transferIndex_injective` | `Dinfty.WeakProdFactorization` |
| `D-1776` | theorem | `transferIndex_surjective` | `Dinfty.WeakProdFactorization` |
| `D-1777` | theorem | `weakProd_uniqueFactorization` | `Dinfty.WeakProdFactorization` |
| `D-1778` | section | `§ Factors of a product with a finite piece` | `Dinfty.WeakProdFactorization` |
| `D-1779` | theorem | `mem_atomFactor_prod_right` | `Dinfty.WeakProdFactorization` |
| `D-1780` | def | `atomFactorProdRightIso` | `Dinfty.WeakProdFactorization` |
| `D-1781` | section | `§ The copy-`A` input: a finite piece's factors are factors of the product` | `Dinfty.WeakProdFactorization` |
| `D-1782` | theorem | `factor_of_prod` | `Dinfty.WeakProdFactorization` |
| `D-1783` | theorem | `factor_index_lt` | `Dinfty.WeakProdFactorization` |
| `D-1784` | section | `§ The left-hand factor, and the converse direction` | `Dinfty.WeakProdFactorization` |
| `D-1785` | theorem | `mem_atomFactor_prod_left` | `Dinfty.WeakProdFactorization` |
| `D-1786` | def | `atomFactorProdLeftIso` | `Dinfty.WeakProdFactorization` |
| `D-1787` | theorem | `factor_index_of_prod` | `Dinfty.WeakProdFactorization` |
| `D-1788` | theorem | `factor_in_finite_piece` | `Dinfty.WeakProdFactorization` |
| `D-1789` | section | `§ The copy-`A` exclusion, assembled` | `Dinfty.WeakProdFactorization` |
| `D-1790` | theorem | `card_atomFactor_le` | `Dinfty.WeakProdFactorization` |
| `D-1791` | theorem | `card_atomFactor_prod_le` | `Dinfty.WeakProdFactorization` |
| `D-1792` | theorem | `no_iso_of_small_pieces` | `Dinfty.WeakProdFactorization` |
| `D-1793` | section | `§ A finite piece on the left as well` | `Dinfty.WeakProdFactorization` |
| `D-1794` | theorem | `isAtom_singleL` | `Dinfty.WeakProdFactorization` |
| `D-1795` | def | `axisIsoL` | `Dinfty.WeakProdFactorization` |
| `D-1796` | theorem | `factor_index_of_prodL` | `Dinfty.WeakProdFactorization` |
| `D-1797` | theorem | `factor_in_finite_pieceL` | `Dinfty.WeakProdFactorization` |
| `D-1798` | theorem | `no_iso_of_small_piecesL` | `Dinfty.WeakProdFactorization` |
| `D-1799` | section | `§ The shape, proved` | `Dinfty.SeedShapeProof` |
| `D-1800` | theorem | `prodEq` | `Dinfty.SeedShapeProof` |
| `D-1801` | abbrev | `Fam` | `Dinfty.SeedShapeProof` |
| `D-1802` | abbrev | `Base` | `Dinfty.SeedShapeProof` |
| `D-1803` | abbrev | `DSeed` | `Dinfty.SeedShapeProof` |
| `D-1804` | section | `§ The level step, dualised` | `Dinfty.SeedShapeProof` |
| `D-1805` | def | `dLevelStep` | `Dinfty.SeedShapeProof` |
| `D-1806` | theorem | `dLevelStep_step` | `Dinfty.SeedShapeProof` |
| `D-1807` | section | `§ The restricted-product side, as an increasing union` | `Dinfty.SeedShapeProof` |
| `D-1808` | abbrev | `Supp` | `Dinfty.SeedShapeProof` |
| `D-1809` | def | `suppStep` | `Dinfty.SeedShapeProof` |
| `D-1810` | def | `suppPres` | `Dinfty.SeedShapeProof` |
| `D-1811` | section | `§ Peeling one coordinate off the finite-support pieces` | `Dinfty.SeedShapeProof` |
| `D-1812` | theorem | `upd_supp` | `Dinfty.SeedShapeProof` |
| `D-1813` | def | `updAt` | `Dinfty.SeedShapeProof` |
| `D-1814` | theorem | `updAt_apply_self` | `Dinfty.SeedShapeProof` |
| `D-1815` | theorem | `updAt_apply_ne` | `Dinfty.SeedShapeProof` |
| `D-1816` | def | `peelFun` | `Dinfty.SeedShapeProof` |
| `D-1817` | def | `peelInv` | `Dinfty.SeedShapeProof` |
| `D-1818` | theorem | `peelInv_peelFun` | `Dinfty.SeedShapeProof` |
| `D-1819` | theorem | `peelFun_peelInv` | `Dinfty.SeedShapeProof` |
| `D-1820` | theorem | `peelFun_le_iff` | `Dinfty.SeedShapeProof` |
| `D-1821` | def | `peelIso` | `Dinfty.SeedShapeProof` |
| `D-1822` | theorem | `peelIso_step` | `Dinfty.SeedShapeProof` |
| `D-1823` | section | `§ The level-wise isomorphism, and the shape` | `Dinfty.SeedShapeProof` |
| `D-1824` | def | `suppZeroIso` | `Dinfty.SeedShapeProof` |
| `D-1825` | def | `levelIso` | `Dinfty.SeedShapeProof` |
| `D-1826` | theorem | `levelIso_step` | `Dinfty.SeedShapeProof` |
| `D-1827` | def | `seedShape` | `Dinfty.SeedShapeProof` |
| `D-1828` | section | `§ The tower's own family satisfies both hypotheses` | `Dinfty.TowerNoAbsorption` |
| `D-1829` | def | `lamD` | `Dinfty.TowerNoAbsorption` |
| `D-1830` | theorem | `lamD_ne_bot` | `Dinfty.TowerNoAbsorption` |
| `D-1831` | theorem | `lamD_le` | `Dinfty.TowerNoAbsorption` |
| `D-1832` | theorem | `lamD_ne_top` | `Dinfty.TowerNoAbsorption` |
| `D-1833` | theorem | `top_ne_bot_D` | `Dinfty.TowerNoAbsorption` |
| `D-1834` | theorem | `tower_no_absorb_two` | `Dinfty.TowerNoAbsorption` |
| `D-1835` | section | `§ The two seeds are not isomorphic — inside `DInfty`` | `Dinfty.SeedsDiffer` |
| `D-1836` | section | `§ Dropping a trivial factor` | `Dinfty.SeedsDiffer` |
| `D-1837` | theorem | `prodEq'` | `Dinfty.SeedsDiffer` |
| `D-1838` | def | `prodUniqueIso` | `Dinfty.SeedsDiffer` |
| `D-1839` | section | `§ The two level-`0` seeds` | `Dinfty.SeedsDiffer` |
| `D-1840` | theorem | `joinIrred_D0_mid` | `Dinfty.SeedsDiffer` |
| `D-1841` | theorem | `val_bot` | `Dinfty.SeedsDiffer` |
| `D-1842` | theorem | `val_mid` | `Dinfty.SeedsDiffer` |
| `D-1843` | theorem | `val_top` | `Dinfty.SeedsDiffer` |
| `D-1844` | theorem | `ne_bot_val` | `Dinfty.SeedsDiffer` |
| `D-1845` | instance | `levelSeedZeroMid_subsingleton` | `Dinfty.SeedsDiffer` |
| `D-1846` | instance | `levelSeedZeroMid_inhabited` | `Dinfty.SeedsDiffer` |
| `D-1847` | instance | `inst-Subsingleton` | `Dinfty.SeedsDiffer` |
| `D-1848` | instance | `inst-Inhabited` | `Dinfty.SeedsDiffer` |
| `D-1849` | section | `§ The level-`0` seed of the top is a two-chain` | `Dinfty.SeedsDiffer` |
| `D-1850` | theorem | `mem_levelSeedZeroTop` | `Dinfty.SeedsDiffer` |
| `D-1851` | def | `topSeedOne` | `Dinfty.SeedsDiffer` |
| `D-1852` | def | `topSeedTwo` | `Dinfty.SeedsDiffer` |
| `D-1853` | theorem | `topSeed_ne` | `Dinfty.SeedsDiffer` |
| `D-1854` | theorem | `fin2_one_ne_zero` | `Dinfty.SeedsDiffer` |
| `D-1855` | theorem | `fin2_cases` | `Dinfty.SeedsDiffer` |
| `D-1856` | def | `finTwoToBase` | `Dinfty.SeedsDiffer` |
| `D-1857` | theorem | `finTwoToBase_zero` | `Dinfty.SeedsDiffer` |
| `D-1858` | theorem | `finTwoToBase_one` | `Dinfty.SeedsDiffer` |
| `D-1859` | theorem | `finTwoToBase_bijective` | `Dinfty.SeedsDiffer` |
| `D-1860` | theorem | `finTwoToBase_le_iff` | `Dinfty.SeedsDiffer` |
| `D-1861` | def | `finTwoToBaseIso` | `Dinfty.SeedsDiffer` |
| `D-1862` | def | `baseTopIso` | `Dinfty.SeedsDiffer` |
| `D-1863` | section | `§ The two seeds are not isomorphic` | `Dinfty.SeedsDiffer` |
| `D-1864` | theorem | `jBelow_midInf_not_iso_topJ` | `Dinfty.SeedsDiffer` |
| `D-1865` | section | `§ The three cardinality facts the copy-`A` step needs` | `Dinfty.TowerCardGrowth` |
| `D-1866` | section | `§ The tower grows` | `Dinfty.TowerCardGrowth` |
| `D-1867` | theorem | `card_D_lt_succ` | `Dinfty.TowerCardGrowth` |
| `D-1868` | theorem | `card_D_strictMono` | `Dinfty.TowerCardGrowth` |
| `D-1869` | theorem | `card_D_lt_of_lt` | `Dinfty.TowerCardGrowth` |
| `D-1870` | section | `§ Join-irreducibles are a proper subtype` | `Dinfty.TowerCardGrowth` |
| `D-1871` | theorem | `card_joinIrred_lt` | `Dinfty.TowerCardGrowth` |
| `D-1872` | section | `§ A proper up-set is smaller` | `Dinfty.TowerCardGrowth` |
| `D-1873` | theorem | `card_upSet_lt` | `Dinfty.TowerCardGrowth` |
| `D-1874` | theorem | `card_upSet_eq_of_bot` | `Dinfty.TowerCardGrowth` |
| `D-1875` | section | `§ The copy-`A` classification: only the marked point survives` | `Dinfty.CopyAClassification` |
| `D-1876` | theorem | `hmk` | `Dinfty.CopyAClassification` |
| `D-1877` | theorem | `hmtk` | `Dinfty.CopyAClassification` |
| `D-1878` | theorem | `hbtk` | `Dinfty.CopyAClassification` |
| `D-1879` | section | `§ The copy-`A` seed, for an arbitrary join-irreducible` | `Dinfty.CopyAClassification` |
| `D-1880` | def | `copyAFunGen` | `Dinfty.CopyAClassification` |
| `D-1881` | theorem | `copyAFunGen_injective` | `Dinfty.CopyAClassification` |
| `D-1882` | theorem | `copyAFunGen_surjective` | `Dinfty.CopyAClassification` |
| `D-1883` | def | `copyAIsoGen` | `Dinfty.CopyAClassification` |
| `D-1884` | section | `§ …and it is a product` | `Dinfty.CopyAClassification` |
| `D-1885` | abbrev | `UpSet` | `Dinfty.CopyAClassification` |
| `D-1886` | def | `upSetDualIso` | `Dinfty.CopyAClassification` |
| `D-1887` | def | `copyASeedIso` | `Dinfty.CopyAClassification` |
| `D-1888` | def | `copyASeedDualIso` | `Dinfty.CopyAClassification` |
| `D-1889` | section | `§ The two cardinality bounds` | `Dinfty.CopyAClassification` |
| `D-1890` | theorem | `card_upSet_lt_D` | `Dinfty.CopyAClassification` |
| `D-1891` | theorem | `card_levelSeed_lt` | `Dinfty.CopyAClassification` |
| `D-1892` | section | `§ The exclusion` | `Dinfty.CopyAClassification` |
| `D-1893` | theorem | `copyA_forces_bot` | `Dinfty.CopyAClassification` |
| `D-1894` | section | `§ The induction step for copy `A`` | `Dinfty.CopyAClassification` |
| `D-1895` | def | `midInfShape` | `Dinfty.CopyAClassification` |
| `D-1896` | def | `shapeComparison` | `Dinfty.CopyAClassification` |
| `D-1897` | theorem | `copyA_step` | `Dinfty.CopyAClassification` |
| `D-1898` | section | `§ The induction, with the copy-`B`/`C` case named` | `Dinfty.CopyAClassification` |
| `D-1899` | def | `CopyBCExcluded` | `Dinfty.CopyAClassification` |
| `D-1900` | theorem | `D0_joinIrred_cases` | `Dinfty.CopyAClassification` |
| `D-1901` | theorem | `seedSeparates_midInf_ji` | `Dinfty.CopyAClassification` |
| `D-1902` | section | `§ …and the consequence for `TwoPointFixed`'s `midInf` half` | `Dinfty.CopyAClassification` |
| `D-1903` | theorem | `fixed_of_seedSeparates_ji` | `Dinfty.CopyAClassification` |
| `D-1904` | theorem | `midInf_fixed` | `Dinfty.CopyAClassification` |
| `D-1905` | section | `§ Copies `B` and `C` are not alike — the seed structure, and a correction` | `Dinfty.CopyBCStructure` |
| `D-1906` | theorem | `hm'` | `Dinfty.CopyBCStructure` |
| `D-1907` | theorem | `hmt'` | `Dinfty.CopyBCStructure` |
| `D-1908` | theorem | `hbt'` | `Dinfty.CopyBCStructure` |
| `D-1909` | section | `§ The marked point is below everything outside copy `A`` | `Dinfty.CopyBCStructure` |
| `D-1910` | theorem | `dMid_eq_glueA` | `Dinfty.CopyBCStructure` |
| `D-1911` | theorem | `dMid_le_glueB` | `Dinfty.CopyBCStructure` |
| `D-1912` | theorem | `dMid_le_glueC` | `Dinfty.CopyBCStructure` |
| `D-1913` | section | `§ Copy `B`: the copy-`A` part of the seed is bounded by the marked point` | `Dinfty.CopyBCStructure` |
| `D-1914` | theorem | `copyA_of_le_glueB_le_dMid` | `Dinfty.CopyBCStructure` |
| `D-1915` | section | `§ Copy `C`: the copy-`A` part reaches strictly above the marked point` | `Dinfty.CopyBCStructure` |
| `D-1916` | theorem | `iotaD_top_eq_glueA` | `Dinfty.CopyBCStructure` |
| `D-1917` | theorem | `dMid_lt_iotaD_top` | `Dinfty.CopyBCStructure` |
| `D-1918` | theorem | `iotaD_top_le_glueC` | `Dinfty.CopyBCStructure` |
| `D-1919` | theorem | `copyC_seed_not_bounded_by_dMid` | `Dinfty.CopyBCStructure` |
| `D-1920` | theorem | `glueB_le_glueC_of_marked_le` | `Dinfty.CopyBCStructure` |
| `D-1921` | theorem | `not_iotaD_top_le_glueB` | `Dinfty.CopyBCStructure` |
| `D-1922` | section | `§ Both halves of `TwoPointFixed`, from one theorem` | `Dinfty.TwoPointAssembly` |
| `D-1923` | theorem | `hmk` | `Dinfty.TwoPointAssembly` |
| `D-1924` | theorem | `hmtk` | `Dinfty.TwoPointAssembly` |
| `D-1925` | theorem | `hbtk` | `Dinfty.TwoPointAssembly` |
| `D-1926` | section | `§ The dualised seed of a join-irreducible has a bottom` | `Dinfty.TwoPointAssembly` |
| `D-1927` | def | `levelSeedDualBot` | `Dinfty.TwoPointAssembly` |
| `D-1928` | section | `§ The copy-`A` exclusion, with an arbitrary finite piece on the left` | `Dinfty.TwoPointAssembly` |
| `D-1929` | theorem | `copyA_forces_bot_gen` | `Dinfty.TwoPointAssembly` |
| `D-1930` | section | `§ The induction step, for any point with the product shape` | `Dinfty.TwoPointAssembly` |
| `D-1931` | theorem | `copyA_step_gen` | `Dinfty.TwoPointAssembly` |
| `D-1932` | section | `§ The induction` | `Dinfty.TwoPointAssembly` |
| `D-1933` | def | `CopyBCExcludedFor` | `Dinfty.TwoPointAssembly` |
| `D-1934` | theorem | `seedSeparates_gen` | `Dinfty.TwoPointAssembly` |
| `D-1935` | section | `§ The two instances` | `Dinfty.TwoPointAssembly` |
| `D-1936` | instance | `inst-OrderBot` | `Dinfty.TwoPointAssembly` |
| `D-1937` | instance | `inst-IsAtomic` | `Dinfty.TwoPointAssembly` |
| `D-1938` | instance | `inst-OrderBot` | `Dinfty.TwoPointAssembly` |
| `D-1939` | instance | `inst-IsAtomic` | `Dinfty.TwoPointAssembly` |
| `D-1940` | theorem | `base_midInf` | `Dinfty.TwoPointAssembly` |
| `D-1941` | theorem | `base_topJ` | `Dinfty.TwoPointAssembly` |
| `D-1942` | theorem | `midInf_fixed` | `Dinfty.TwoPointAssembly` |
| `D-1943` | theorem | `topJ_fixed` | `Dinfty.TwoPointAssembly` |
| `D-1944` | theorem | `twoPointFixed` | `Dinfty.TwoPointAssembly` |
| `D-1945` | section | `§ Copy `B`, part 1: the split, and the pieces the argument needs` | `Dinfty.CopyBExclusion` |
| `D-1946` | theorem | `hmk'` | `Dinfty.CopyBExclusion` |
| `D-1947` | theorem | `hmtk'` | `Dinfty.CopyBExclusion` |
| `D-1948` | theorem | `hbtk'` | `Dinfty.CopyBExclusion` |
| `D-1949` | instance | `obMid` | `Dinfty.CopyBExclusion` |
| `D-1950` | instance | `obTop` | `Dinfty.CopyBExclusion` |
| `D-1951` | section | `§ The case split, restated at the tower` | `Dinfty.CopyBExclusion` |
| `D-1952` | theorem | `canonBFix` | `Dinfty.CopyBExclusion` |
| `D-1953` | theorem | `canonCFixBot` | `Dinfty.CopyBExclusion` |
| `D-1954` | theorem | `dSuccCases` | `Dinfty.CopyBExclusion` |
| `D-1955` | section | `§ Splitting the obligation` | `Dinfty.CopyBExclusion` |
| `D-1956` | theorem | `copyBC_of_B_and_C` | `Dinfty.CopyBExclusion` |
| `D-1957` | section | `§ Generation at the two left-hand pieces` | `Dinfty.CopyBExclusion` |
| `D-1958` | theorem | `genByFactors_of_subsingleton` | `Dinfty.CopyBExclusion` |
| `D-1959` | theorem | `genByFactors_of_atom_unique` | `Dinfty.CopyBExclusion` |
| `D-1960` | theorem | `genByFactors_base_midInf` | `Dinfty.CopyBExclusion` |
| `D-1961` | section | `§ `topJ`'s left-hand piece is a two-chain, so it has a unique atom` | `Dinfty.CopyBExclusion` |
| `D-1962` | def | `topAtom` | `Dinfty.CopyBExclusion` |
| `D-1963` | theorem | `isAtom_topAtom` | `Dinfty.CopyBExclusion` |
| `D-1964` | theorem | `atom_base_top_unique` | `Dinfty.CopyBExclusion` |
| `D-1965` | theorem | `genByFactors_base_topJ` | `Dinfty.CopyBExclusion` |
| `D-1966` | section | `§ The two witnesses inside a copy-`B` seed` | `Dinfty.CopyBExclusion` |
| `D-1967` | def | `dMidSeed` | `Dinfty.CopyBExclusion` |
| `D-1968` | def | `gLow` | `Dinfty.CopyBExclusion` |
| `D-1969` | theorem | `gLow_joinIrred` | `Dinfty.CopyBExclusion` |
| `D-1970` | theorem | `gLow_le` | `Dinfty.CopyBExclusion` |
| `D-1971` | theorem | `gLow_ne` | `Dinfty.CopyBExclusion` |
| `D-1972` | theorem | `gLow_lt` | `Dinfty.CopyBExclusion` |
| `D-1973` | def | `wSeed` | `Dinfty.CopyBExclusion` |
| `D-1974` | theorem | `wSeed_lt_dMidSeed` | `Dinfty.CopyBExclusion` |
| `D-1975` | section | `§ What copy `B` needs — now supplied in `Dinfty/CopyBAtoms.lean`` | `Dinfty.CopyBExclusion` |
| `D-1976` | section | `§ The seam is not join-irreducible` | `Dinfty.CopyBExclusion` |
| `D-1977` | theorem | `seam_not_joinIrred` | `Dinfty.CopyBExclusion` |
| `D-1978` | theorem | `copyB_ne_top` | `Dinfty.CopyBExclusion` |
| `D-1979` | section | `§ The §79 scoping note, made a theorem: both `liftGenM` thresholds are join-prime` | `Dinfty.JoinPrime` |
| `D-1980` | section | `§ The notion` | `Dinfty.JoinPrime` |
| `D-1981` | def | `JoinPrime` | `Dinfty.JoinPrime` |
| `D-1982` | theorem | `joinPrime_of_total` | `Dinfty.JoinPrime` |
| `D-1983` | section | `§ `⊤` is join-prime whenever the coatom is unique` | `Dinfty.JoinPrime` |
| `D-1984` | theorem | `top_joinPrime` | `Dinfty.JoinPrime` |
| `D-1985` | section | `§ Constants` | `Dinfty.JoinPrime` |
| `D-1986` | theorem | `constHom_joinPrime` | `Dinfty.JoinPrime` |
| `D-1987` | theorem | `top_endP_joinPrime` | `Dinfty.JoinPrime` |
| `D-1988` | section | `§ The inductive step at the tower` | `Dinfty.JoinPrime` |
| `D-1989` | theorem | `dMid_succ_joinPrime` | `Dinfty.JoinPrime` |
| `D-1990` | theorem | `dMid_zero_joinPrime` | `Dinfty.JoinPrime` |
| `D-1991` | theorem | `dMid_joinPrime` | `Dinfty.JoinPrime` |
| `D-1992` | theorem | `markedPt_joinPrime` | `Dinfty.JoinPrime` |
| `D-1993` | theorem | `top_D_joinPrime` | `Dinfty.JoinPrime` |
| `D-1994` | theorem | `top_endP_D_joinPrime` | `Dinfty.JoinPrime` |
| `D-1995` | section | `§ What join-primality buys` | `Dinfty.JoinPrime` |
| `D-1996` | theorem | `ite_threshold_sup` | `Dinfty.JoinPrime` |
| `D-1997` | theorem | `markedPt_ite_sup` | `Dinfty.JoinPrime` |
| `D-1998` | theorem | `top_ite_sup` | `Dinfty.JoinPrime` |
| `D-1999` | section | `§ Both ingredients of `glueAA` preserve binary joins` | `Dinfty.JoinPrime` |
| `D-2000` | theorem | `iotaD_sup` | `Dinfty.JoinPrime` |
| `D-2001` | theorem | `iotaEndP_sup` | `Dinfty.JoinPrime` |
| `D-2002` | def | `liftVal` | `Dinfty.JoinPrime` |
| `D-2003` | theorem | `liftVal_sup` | `Dinfty.JoinPrime` |
| `D-2004` | theorem | `glueAA_ingredients_sup` | `Dinfty.JoinPrime` |
| `D-2005` | section | `§ Rigidity through the join-irreducibles — the half of Birkhoff that is free` | `Dinfty.JoinIrredRigidity` |
| `D-2006` | section | `§ Order isomorphisms preserve finite sups` | `Dinfty.JoinIrredRigidity` |
| `D-2007` | theorem | `orderIso_finset_sup` | `Dinfty.JoinIrredRigidity` |
| `D-2008` | section | `§ The easy half of Birkhoff` | `Dinfty.JoinIrredRigidity` |
| `D-2009` | theorem | `eq_of_agree_on_joinIrred` | `Dinfty.JoinIrredRigidity` |
| `D-2010` | theorem | `eq_refl_of_fixes_joinIrred` | `Dinfty.JoinIrredRigidity` |
| `D-2011` | section | `§ The threshold argument at `EndP`` | `Dinfty.JoinIrredRigidity` |
| `D-2012` | theorem | `constHom_finset_sup` | `Dinfty.JoinIrredRigidity` |
| `D-2013` | theorem | `sigma_eq_id_of_rigid` | `Dinfty.JoinIrredRigidity` |
| `D-2014` | theorem | `fixes_constHom_of_rigid` | `Dinfty.JoinIrredRigidity` |
| `D-2015` | section | `§ `EndP P` is rigid whenever `P` is — CONJ′ was already a theorem` | `Dinfty.EndPRigid` |
| `D-2016` | def | `jiRestrict` | `Dinfty.EndPRigid` |
| `D-2017` | theorem | `jiRestrict_ord` | `Dinfty.EndPRigid` |
| `D-2018` | theorem | `endP_rigid` | `Dinfty.EndPRigid` |
| `D-2019` | section | `§ Ingredient 2: `Φ_tri_v2` is a functor` | `Dinfty.PhiTriFunctor` |
| `D-2020` | section | `§ Tripointed morphisms` | `Dinfty.PhiTriFunctor` |
| `D-2021` | structure | `TriHom` | `Dinfty.PhiTriFunctor` |
| `D-2022` | def | `id` | `Dinfty.PhiTriFunctor` |
| `D-2023` | def | `comp` | `Dinfty.PhiTriFunctor` |
| `D-2024` | section | `§ `baseMapGen` is tagwise-functorial` | `Dinfty.PhiTriFunctor` |
| `D-2025` | theorem | `baseMapGen_id` | `Dinfty.PhiTriFunctor` |
| `D-2026` | theorem | `baseMapGen_comp` | `Dinfty.PhiTriFunctor` |
| `D-2027` | section | `§ The glued order is carried across` | `Dinfty.PhiTriFunctor` |
| `D-2028` | theorem | `rawRuleGen_map` | `Dinfty.PhiTriFunctor` |
| `D-2029` | theorem | `occsGen_map` | `Dinfty.PhiTriFunctor` |
| `D-2030` | theorem | `leGlueGen_map` | `Dinfty.PhiTriFunctor` |
| `D-2031` | theorem | `occsGen_mem_canon` | `Dinfty.PhiTriFunctor` |
| `D-2032` | theorem | `leGlueGen_canon` | `Dinfty.PhiTriFunctor` |
| `D-2033` | section | `§ The descent` | `Dinfty.PhiTriFunctor` |
| `D-2034` | theorem | `canonGen_baseMapGen_canon` | `Dinfty.PhiTriFunctor` |
| `D-2035` | section | `§ `Φ` on objects: the three distinguished points` | `Dinfty.PhiTriFunctor` |
| `D-2036` | def | `triBot` | `Dinfty.PhiTriFunctor` |
| `D-2037` | def | `triMark` | `Dinfty.PhiTriFunctor` |
| `D-2038` | def | `triTop` | `Dinfty.PhiTriFunctor` |
| `D-2039` | theorem | `triBot_le` | `Dinfty.PhiTriFunctor` |
| `D-2040` | theorem | `le_triTop` | `Dinfty.PhiTriFunctor` |
| `D-2041` | theorem | `triMark_ne_triBot` | `Dinfty.PhiTriFunctor` |
| `D-2042` | theorem | `triMark_ne_triTop` | `Dinfty.PhiTriFunctor` |
| `D-2043` | theorem | `triBot_ne_triTop` | `Dinfty.PhiTriFunctor` |
| `D-2044` | section | `§ `Φ` on morphisms, and the functor laws` | `Dinfty.PhiTriFunctor` |
| `D-2045` | def | `phiFun` | `Dinfty.PhiTriFunctor` |
| `D-2046` | theorem | `phiFun_val` | `Dinfty.PhiTriFunctor` |
| `D-2047` | theorem | `phiFun_id` | `Dinfty.PhiTriFunctor` |
| `D-2048` | theorem | `phiFun_comp` | `Dinfty.PhiTriFunctor` |
| `D-2049` | theorem | `phiFun_monotone` | `Dinfty.PhiTriFunctor` |
| `D-2050` | section | `§ `Φ g` is again tripointed` | `Dinfty.PhiTriFunctor` |
| `D-2051` | theorem | `phiFun_triBot` | `Dinfty.PhiTriFunctor` |
| `D-2052` | theorem | `phiFun_triMark` | `Dinfty.PhiTriFunctor` |
| `D-2053` | theorem | `phiFun_triTop` | `Dinfty.PhiTriFunctor` |
| `D-2054` | section | `§ Ingredient 2, in one statement` | `Dinfty.PhiTriFunctor` |
| `D-2055` | theorem | `phi_functor_laws` | `Dinfty.PhiTriFunctor` |
| `D-2056` | section | `§ The identification: when is a tripointed action `Φ`'s action?` | `Dinfty.PhiTriIdentification` |
| `D-2057` | def | `phiTwist` | `Dinfty.PhiTriIdentification` |
| `D-2058` | theorem | `phiTwist_val` | `Dinfty.PhiTriIdentification` |
| `D-2059` | theorem | `glueTwist_self` | `Dinfty.PhiTriIdentification` |
| `D-2060` | theorem | `phiTwist_self` | `Dinfty.PhiTriIdentification` |
| `D-2061` | section | `§ Every `phiTwist` is a monotone tripointed action` | `Dinfty.PhiTriIdentification` |
| `D-2062` | theorem | `phiTwist_monotone` | `Dinfty.PhiTriIdentification` |
| `D-2063` | theorem | `phiTwist_triBot` | `Dinfty.PhiTriIdentification` |
| `D-2064` | theorem | `phiTwist_triMark` | `Dinfty.PhiTriIdentification` |
| `D-2065` | theorem | `phiTwist_triTop` | `Dinfty.PhiTriIdentification` |
| `D-2066` | section | `§ The criterion` | `Dinfty.PhiTriIdentification` |
| `D-2067` | theorem | `phiTwist_eq_phiFun_iff` | `Dinfty.PhiTriIdentification` |
| `D-2068` | section | `§ What closes the identification` | `Dinfty.PhiTriIdentification` |
| `D-2069` | theorem | `triHom_toFun_eq_id` | `Dinfty.PhiTriIdentification` |
| `D-2070` | theorem | `phiTwist_eq_phiFun_of_rigid` | `Dinfty.PhiTriIdentification` |
| `D-2071` | theorem | `phiTwist_eq_phiFun_id` | `Dinfty.PhiTriIdentification` |
| `D-2072` | section | `§ The bridge: `Φ_tri_v2` **is** the tower's step` | `Dinfty.PhiTriTower` |
| `D-2073` | section | `§ The `Gen` layer is the finite layer` | `Dinfty.PhiTriTower` |
| `D-2074` | theorem | `canon_eq` | `Dinfty.PhiTriTower` |
| `D-2075` | theorem | `glueCar_eq` | `Dinfty.PhiTriTower` |
| `D-2076` | theorem | `rawRule_eq` | `Dinfty.PhiTriTower` |
| `D-2077` | theorem | `occs_eq` | `Dinfty.PhiTriTower` |
| `D-2078` | theorem | `leGlue_eq` | `Dinfty.PhiTriTower` |
| `D-2079` | theorem | `baseMap_eq` | `Dinfty.PhiTriTower` |
| `D-2080` | theorem | `phiFun_eq_glueMap` | `Dinfty.PhiTriTower` |
| `D-2081` | section | `§ The tower` | `Dinfty.PhiTriTower` |
| `D-2082` | abbrev | `TowerHom` | `Dinfty.PhiTriTower` |
| `D-2083` | theorem | `hmk` | `Dinfty.PhiTriTower` |
| `D-2084` | theorem | `hmtk` | `Dinfty.PhiTriTower` |
| `D-2085` | theorem | `hbtk` | `Dinfty.PhiTriTower` |
| `D-2086` | section | `§ The bridge at the tower — all `rfl`` | `Dinfty.PhiTriTower` |
| `D-2087` | theorem | `D_succ_eq` | `Dinfty.PhiTriTower` |
| `D-2088` | theorem | `le_succ_eq` | `Dinfty.PhiTriTower` |
| `D-2089` | theorem | `dMid_succ_eq` | `Dinfty.PhiTriTower` |
| `D-2090` | theorem | `bot_succ_eq` | `Dinfty.PhiTriTower` |
| `D-2091` | theorem | `top_succ_eq` | `Dinfty.PhiTriTower` |
| `D-2092` | section | `§ `Φ` on the tower` | `Dinfty.PhiTriTower` |
| `D-2093` | instance | `finiteEndPD` | `Dinfty.PhiTriTower` |
| `D-2094` | def | `phiTower` | `Dinfty.PhiTriTower` |
| `D-2095` | def | `phiTowerD` | `Dinfty.PhiTriTower` |
| `D-2096` | theorem | `phiTower_id` | `Dinfty.PhiTriTower` |
| `D-2097` | theorem | `phiTower_comp` | `Dinfty.PhiTriTower` |
| `D-2098` | theorem | `phiTower_monotone` | `Dinfty.PhiTriTower` |
| `D-2099` | theorem | `phiTower_triBot` | `Dinfty.PhiTriTower` |
| `D-2100` | theorem | `phiTower_triMark` | `Dinfty.PhiTriTower` |
| `D-2101` | theorem | `phiTower_triTop` | `Dinfty.PhiTriTower` |
| `D-2102` | theorem | `phiTower_eq_glueMap` | `Dinfty.PhiTriTower` |
| `D-2103` | theorem | `phiTower_unique_of_rigid` | `Dinfty.PhiTriTower` |
| `D-2104` | section | `§ The hypothesis discharged: `EndP (D k)` is rigid` | `Dinfty.PhiTriTower` |
| `D-2105` | theorem | `joinIrred_lamD` | `Dinfty.PhiTriTower` |
| `D-2106` | instance | `nonemptyJD` | `Dinfty.PhiTriTower` |
| `D-2107` | theorem | `endP_D_rigid` | `Dinfty.PhiTriTower` |
| `D-2108` | theorem | `phiTower_unique` | `Dinfty.PhiTriTower` |
| `D-2109` | section | `§ The obstruction is one-directional: `Φ` acts on the tower's **projections**` | `Dinfty.ProjectionTripointed` |
| `D-2110` | section | `§ The projection is tripointed` | `Dinfty.ProjectionTripointed` |
| `D-2111` | def | `pEndPHom` | `Dinfty.ProjectionTripointed` |
| `D-2112` | theorem | `pEndPHom_apply` | `Dinfty.ProjectionTripointed` |
| `D-2113` | theorem | `pEndP_markedPt` | `Dinfty.ProjectionTripointed` |
| `D-2114` | def | `pTri` | `Dinfty.ProjectionTripointed` |
| `D-2115` | theorem | `pTri_toFun` | `Dinfty.ProjectionTripointed` |
| `D-2116` | section | `§ The embedding is not` | `Dinfty.ProjectionTripointed` |
| `D-2117` | theorem | `iotaEndP_top_ne_top` | `Dinfty.ProjectionTripointed` |
| `D-2118` | theorem | `no_towerHom_iotaEndP` | `Dinfty.ProjectionTripointed` |
| `D-2119` | section | `§ `Φ` applied to the projection` | `Dinfty.ProjectionTripointed` |
| `D-2120` | def | `phiP` | `Dinfty.ProjectionTripointed` |
| `D-2121` | theorem | `phiP_val` | `Dinfty.ProjectionTripointed` |
| `D-2122` | theorem | `phiP_monotone` | `Dinfty.ProjectionTripointed` |
| `D-2123` | section | `§ Values on the three copies` | `Dinfty.ProjectionTripointed` |
| `D-2124` | theorem | `phiP_tagA` | `Dinfty.ProjectionTripointed` |
| `D-2125` | theorem | `phiP_bot` | `Dinfty.ProjectionTripointed` |
| `D-2126` | theorem | `phiP_mid` | `Dinfty.ProjectionTripointed` |
| `D-2127` | theorem | `phiP_top` | `Dinfty.ProjectionTripointed` |
| `D-2128` | section | `§ The retraction: `Φ(p) ∘ glueAA = id`` | `Dinfty.ProjectionTripointed` |
| `D-2129` | theorem | `pEndP_liftGenM` | `Dinfty.ProjectionTripointed` |
| `D-2130` | theorem | `pEndP_iotaEndPGenM` | `Dinfty.ProjectionTripointed` |
| `D-2131` | theorem | `phiP_glueAA` | `Dinfty.ProjectionTripointed` |
| `D-2132` | section | `§ But it is **not** an ep-pair: the deflation fails` | `Dinfty.ProjectionTripointed` |
| `D-2133` | theorem | `constHom_iotaD_top_ne_bot` | `Dinfty.ProjectionTripointed` |
| `D-2134` | theorem | `constHom_iotaD_top_ne_top` | `Dinfty.ProjectionTripointed` |
| `D-2135` | theorem | `pEndP_constHom_iotaD_top` | `Dinfty.ProjectionTripointed` |
| `D-2136` | theorem | `not_glueAA_phiP_deflation` | `Dinfty.ProjectionTripointed` |
| `D-2137` | structure | `EpPairTower` | `Dinfty.EpPairTower` |
| `D-2138` | theorem | `emb_prj_le` | `Dinfty.EpPairTower` |
| `D-2139` | section | `§ Iterated embedding / projection along the chain` | `Dinfty.EpPairTower` |
| `D-2140` | def | `embLe` | `Dinfty.EpPairTower` |
| `D-2141` | def | `prjLe` | `Dinfty.EpPairTower` |
| `D-2142` | theorem | `embLe_self` | `Dinfty.EpPairTower` |
| `D-2143` | theorem | `embLe_succ` | `Dinfty.EpPairTower` |
| `D-2144` | theorem | `embLe_trans` | `Dinfty.EpPairTower` |
| `D-2145` | theorem | `prjLe_self` | `Dinfty.EpPairTower` |
| `D-2146` | theorem | `prjLe_succ` | `Dinfty.EpPairTower` |
| `D-2147` | theorem | `embLe_mono` | `Dinfty.EpPairTower` |
| `D-2148` | theorem | `prjLe_mono` | `Dinfty.EpPairTower` |
| `D-2149` | theorem | `prj_prjLe_comm` | `Dinfty.EpPairTower` |
| `D-2150` | theorem | `prjLe_trans` | `Dinfty.EpPairTower` |
| `D-2151` | theorem | `prj_embLe` | `Dinfty.EpPairTower` |
| `D-2152` | theorem | `emb_le_iff` | `Dinfty.EpPairTower` |
| `D-2153` | theorem | `embLe_le_iff` | `Dinfty.EpPairTower` |
| `D-2154` | theorem | `embLe_injective` | `Dinfty.EpPairTower` |
| `D-2155` | section | `§ The bilimit` | `Dinfty.EpPairTower` |
| `D-2156` | def | `Bilim` | `Dinfty.EpPairTower` |
| `D-2157` | instance | `inst-PartialOrder` | `Dinfty.EpPairTower` |
| `D-2158` | theorem | `Bilim.le_def` | `Dinfty.EpPairTower` |
| `D-2159` | theorem | `Bilim_prjLe_eq` | `Dinfty.EpPairTower` |
| `D-2160` | theorem | `Bilim.emb_le` | `Dinfty.EpPairTower` |
| `D-2161` | section | `§ The staged sequence of a compact` | `Dinfty.EpPairTower` |
| `D-2162` | def | `seqOf` | `Dinfty.EpPairTower` |
| `D-2163` | theorem | `seqOf_compat` | `Dinfty.EpPairTower` |
| `D-2164` | theorem | `seqOf_emb_step` | `Dinfty.EpPairTower` |
| `D-2165` | theorem | `seqOf_embLe_invariant` | `Dinfty.EpPairTower` |
| `D-2166` | section | `§ `ins` : the canonical embedding of level `k` into the bilimit` | `Dinfty.EpPairTower` |
| `D-2167` | def | `ins` | `Dinfty.EpPairTower` |
| `D-2168` | theorem | `ins_apply` | `Dinfty.EpPairTower` |
| `D-2169` | theorem | `ins_self` | `Dinfty.EpPairTower` |
| `D-2170` | theorem | `ins_emb` | `Dinfty.EpPairTower` |
| `D-2171` | theorem | `ins_embLe` | `Dinfty.EpPairTower` |
| `D-2172` | theorem | `ins_monotone` | `Dinfty.EpPairTower` |
| `D-2173` | theorem | `embLe_bilim_le` | `Dinfty.EpPairTower` |
| `D-2174` | theorem | `ins_le_self` | `Dinfty.EpPairTower` |
| `D-2175` | theorem | `ins_chain_mono` | `Dinfty.EpPairTower` |
| `D-2176` | section | `§ dcpo structure` | `Dinfty.EpPairTower` |
| `D-2177` | structure | `IsDcpo` | `Dinfty.EpPairTower` |
| `D-2178` | theorem | `Bilim_directed_image` | `Dinfty.EpPairTower` |
| `D-2179` | theorem | `Bilim_levelwise_isLUB` | `Dinfty.EpPairTower` |
| `D-2180` | theorem | `exists_levelwise_lub` | `Dinfty.EpPairTower` |
| `D-2181` | theorem | `Bilim.exists_isLUB_of_directedOn` | `Dinfty.EpPairTower` |
| `D-2182` | section | `§ The approximating chain of a bilimit point` | `Dinfty.EpPairTower` |
| `D-2183` | def | `chainSet` | `Dinfty.EpPairTower` |
| `D-2184` | theorem | `chainSet_nonempty` | `Dinfty.EpPairTower` |
| `D-2185` | theorem | `chainSet_directedOn` | `Dinfty.EpPairTower` |
| `D-2186` | theorem | `chainSet_isLUB` | `Dinfty.EpPairTower` |
| `D-2187` | theorem | `isLUB_bilim_apply` | `Dinfty.EpPairTower` |
| `D-2188` | theorem | `seqOf_eq_embLe` | `Dinfty.EpPairTower` |
| `D-2189` | section | `§ Colimit cocones over the tower` | `Dinfty.EpPairTower` |
| `D-2190` | structure | `IsColimitCocone` | `Dinfty.EpPairTower` |
| `D-2191` | theorem | `proj_tower` | `Dinfty.EpPairTower` |
| `D-2192` | theorem | `proj_prjLe` | `Dinfty.EpPairTower` |
| `D-2193` | def | `toBilim` | `Dinfty.EpPairTower` |
| `D-2194` | theorem | `toBilim_apply` | `Dinfty.EpPairTower` |
| `D-2195` | theorem | `toBilim_le_iff` | `Dinfty.EpPairTower` |
| `D-2196` | theorem | `toBilim_injective` | `Dinfty.EpPairTower` |
| `D-2197` | theorem | `toBilim_surjective` | `Dinfty.EpPairTower` |
| `D-2198` | def | `orderIsoBilim` | `Dinfty.EpPairTower` |
| `D-2199` | theorem | `Bilim_isColimitCocone` | `Dinfty.EpPairTower` |
| `D-2200` | def | `isColimitCocone_orderIso` | `Dinfty.EpPairTower` |
| `D-2201` | section | `§ The tower shift, and what Theorem A reduces to` | `Dinfty.TowerShift` |
| `D-2202` | section | `§ The shifted tower` | `Dinfty.TowerShift` |
| `D-2203` | def | `shift` | `Dinfty.TowerShift` |
| `D-2204` | theorem | `shift_carrier` | `Dinfty.TowerShift` |
| `D-2205` | theorem | `shift_prj` | `Dinfty.TowerShift` |
| `D-2206` | theorem | `shift_emb` | `Dinfty.TowerShift` |
| `D-2207` | section | `§ The bilimit does not see the shift` | `Dinfty.TowerShift` |
| `D-2208` | def | `shiftFwd` | `Dinfty.TowerShift` |
| `D-2209` | def | `unshiftSeq` | `Dinfty.TowerShift` |
| `D-2210` | theorem | `unshiftSeq_compat` | `Dinfty.TowerShift` |
| `D-2211` | def | `unshift` | `Dinfty.TowerShift` |
| `D-2212` | def | `shiftIso` | `Dinfty.TowerShift` |
| `D-2213` | section | `§ Theorem A, reduced to one obligation` | `Dinfty.TowerShift` |
| `D-2214` | def | `orderIsoBilim_shift` | `Dinfty.TowerShift` |
| `D-2215` | section | `§ §79's question, as a single named `Prop` — and what answering it would give` | `Dinfty.GlueAAEpPartner` |
| `D-2216` | def | `GlueAAJoinPreserving` | `Dinfty.GlueAAEpPartner` |
| `D-2217` | section | `§ The two hypotheses that are not the question` | `Dinfty.GlueAAEpPartner` |
| `D-2218` | theorem | `iotaEndP_bot` | `Dinfty.GlueAAEpPartner` |
| `D-2219` | theorem | `glueAA_bot` | `Dinfty.GlueAAEpPartner` |
| `D-2220` | section | `§ What the question buys` | `Dinfty.GlueAAEpPartner` |
| `D-2221` | theorem | `exists_glueAA_epPartner` | `Dinfty.GlueAAEpPartner` |
| `D-2222` | def | `qAA` | `Dinfty.GlueAAEpPartner` |
| `D-2223` | def | `fTower` | `Dinfty.GlueAAEpPartner` |
| `D-2224` | theorem | `fTower_carrier` | `Dinfty.GlueAAEpPartner` |
| `D-2225` | theorem | `fTower_emb` | `Dinfty.GlueAAEpPartner` |
| `D-2226` | section | `§ `glueAA` preserves binary joins — the tag lemmas` | `Dinfty.GlueAAJoin` |
| `D-2227` | section | `§ `liftGenM`, declared at the tower` | `Dinfty.GlueAAJoin` |
| `D-2228` | def | `liftT` | `Dinfty.GlueAAJoin` |
| `D-2229` | theorem | `liftT_apply` | `Dinfty.GlueAAJoin` |
| `D-2230` | theorem | `liftT_bot` | `Dinfty.GlueAAJoin` |
| `D-2231` | theorem | `liftT_mid` | `Dinfty.GlueAAJoin` |
| `D-2232` | theorem | `liftT_top` | `Dinfty.GlueAAJoin` |
| `D-2233` | theorem | `liftT_eq_bot_iff` | `Dinfty.GlueAAJoin` |
| `D-2234` | theorem | `liftT_eq_mid_iff` | `Dinfty.GlueAAJoin` |
| `D-2235` | theorem | `liftT_monotone` | `Dinfty.GlueAAJoin` |
| `D-2236` | theorem | `liftT_ne_bot` | `Dinfty.GlueAAJoin` |
| `D-2237` | theorem | `liftT_ne_mid` | `Dinfty.GlueAAJoin` |
| `D-2238` | theorem | `liftT_sup` | `Dinfty.GlueAAJoin` |
| `D-2239` | section | `§ The two guards` | `Dinfty.GlueAAJoin` |
| `D-2240` | theorem | `iotaEndP_le_marked_iff` | `Dinfty.GlueAAJoin` |
| `D-2241` | theorem | `marked_le_liftT_iff` | `Dinfty.GlueAAJoin` |
| `D-2242` | section | `§ `glueAA` on the three copies, canon-free` | `Dinfty.GlueAAJoin` |
| `D-2243` | theorem | `glueAA_glueA` | `Dinfty.GlueAAJoin` |
| `D-2244` | theorem | `glueAA_glueB` | `Dinfty.GlueAAJoin` |
| `D-2245` | theorem | `glueAA_glueC` | `Dinfty.GlueAAJoin` |
| `D-2246` | section | `§ The join, read on values` | `Dinfty.GlueAAJoin` |
| `D-2247` | theorem | `sup_val` | `Dinfty.GlueAAJoin` |
| `D-2248` | section | `§ `canon` and `glueJoinRaw`, one branch at a time` | `Dinfty.GlueAAJoin` |
| `D-2249` | theorem | `canon_inl` | `Dinfty.GlueAAJoin` |
| `D-2250` | theorem | `canon_inrl_of_ne` | `Dinfty.GlueAAJoin` |
| `D-2251` | theorem | `canon_inrr_of_ne` | `Dinfty.GlueAAJoin` |
| `D-2252` | theorem | `canon_inrr_mid` | `Dinfty.GlueAAJoin` |
| `D-2253` | theorem | `gjr_AA` | `Dinfty.GlueAAJoin` |
| `D-2254` | theorem | `gjr_BB` | `Dinfty.GlueAAJoin` |
| `D-2255` | theorem | `gjr_CC` | `Dinfty.GlueAAJoin` |
| `D-2256` | theorem | `gjr_AC` | `Dinfty.GlueAAJoin` |
| `D-2257` | theorem | `gjr_CA` | `Dinfty.GlueAAJoin` |
| `D-2258` | theorem | `gjr_AB_pos` | `Dinfty.GlueAAJoin` |
| `D-2259` | theorem | `gjr_AB_neg` | `Dinfty.GlueAAJoin` |
| `D-2260` | theorem | `gjr_BA_pos` | `Dinfty.GlueAAJoin` |
| `D-2261` | theorem | `gjr_BA_neg` | `Dinfty.GlueAAJoin` |
| `D-2262` | theorem | `gjr_BC_pos` | `Dinfty.GlueAAJoin` |
| `D-2263` | theorem | `gjr_BC_neg` | `Dinfty.GlueAAJoin` |
| `D-2264` | theorem | `gjr_CB_pos` | `Dinfty.GlueAAJoin` |
| `D-2265` | theorem | `gjr_CB_neg` | `Dinfty.GlueAAJoin` |
| `D-2266` | theorem | `canonC_ne_mid` | `Dinfty.GlueAAJoin` |
| `D-2267` | theorem | `sup_ne_bot_of_left` | `Dinfty.GlueAAJoin` |
| `D-2268` | section | `§ The tagwise payload map` | `Dinfty.GlueAAJoin` |
| `D-2269` | def | `tagMap` | `Dinfty.GlueAAJoin` |
| `D-2270` | theorem | `tagMap_inl` | `Dinfty.GlueAAJoin` |
| `D-2271` | theorem | `tagMap_inrl` | `Dinfty.GlueAAJoin` |
| `D-2272` | theorem | `tagMap_inrr` | `Dinfty.GlueAAJoin` |
| `D-2273` | theorem | `glueAA_val` | `Dinfty.GlueAAJoin` |
| `D-2274` | theorem | `canon_tagMap` | `Dinfty.GlueAAJoin` |
| `D-2275` | section | `§ The nine cases` | `Dinfty.GlueAAJoin` |
| `D-2276` | theorem | `core` | `Dinfty.GlueAAJoin` |
| `D-2277` | theorem | `glueAA_sup` | `Dinfty.GlueAAJoin` |
| `D-2278` | theorem | `glueAAJoinPreserving` | `Dinfty.GlueAAJoin` |
| `D-2279` | def | `fTowerReal` | `Dinfty.GlueAAJoin` |
| `D-2280` | theorem | `fTowerReal_carrier` | `Dinfty.GlueAAJoin` |
| `D-2281` | theorem | `fTowerReal_emb` | `Dinfty.GlueAAJoin` |
| `D-2282` | section | `§ Obstruction (T) does not apply to the F-tower` | `Dinfty.FTowerTripointed` |
| `D-2283` | section | `§ The embedding is tripointed` | `Dinfty.FTowerTripointed` |
| `D-2284` | theorem | `iotaEndP_markedPt` | `Dinfty.FTowerTripointed` |
| `D-2285` | theorem | `glueAA_mid` | `Dinfty.FTowerTripointed` |
| `D-2286` | theorem | `top_eq_glueC` | `Dinfty.FTowerTripointed` |
| `D-2287` | theorem | `glueAA_top` | `Dinfty.FTowerTripointed` |
| `D-2288` | theorem | `glueAA_tripointed` | `Dinfty.FTowerTripointed` |
| `D-2289` | theorem | `iotaD_not_top_but_glueAA_is` | `Dinfty.FTowerTripointed` |
| `D-2290` | section | `§ …hence so is the projection` | `Dinfty.FTowerTripointed` |
| `D-2291` | theorem | `qAA_glueAA` | `Dinfty.FTowerTripointed` |
| `D-2292` | theorem | `qAA_bot` | `Dinfty.FTowerTripointed` |
| `D-2293` | theorem | `qAA_mid` | `Dinfty.FTowerTripointed` |
| `D-2294` | theorem | `qAA_top` | `Dinfty.FTowerTripointed` |
| `D-2295` | section | `§ The three points assemble along the F-tower` | `Dinfty.FTowerTripointed` |
| `D-2296` | def | `botF` | `Dinfty.FTowerTripointed` |
| `D-2297` | def | `midF` | `Dinfty.FTowerTripointed` |
| `D-2298` | def | `topF` | `Dinfty.FTowerTripointed` |
| `D-2299` | theorem | `botF_le` | `Dinfty.FTowerTripointed` |
| `D-2300` | theorem | `le_topF` | `Dinfty.FTowerTripointed` |
| `D-2301` | instance | `inst-OrderBot` | `Dinfty.FTowerTripointed` |
| `D-2302` | instance | `inst-OrderTop` | `Dinfty.FTowerTripointed` |
| `D-2303` | instance | `inst-BoundedOrder` | `Dinfty.FTowerTripointed` |
| `D-2304` | theorem | `midF_ne_botF` | `Dinfty.FTowerTripointed` |
| `D-2305` | theorem | `midF_ne_topF` | `Dinfty.FTowerTripointed` |
| `D-2306` | theorem | `bilim_tripointed` | `Dinfty.FTowerTripointed` |
| `D-2307` | section | `§ But the F-tower is **not** the `Φ`-iterate tower` | `Dinfty.FTowerTripointed` |
| `D-2308` | theorem | `glueAA_top_ne_iotaD_top` | `Dinfty.FTowerTripointed` |
| `D-2309` | theorem | `fTower_not_phi_iterate` | `Dinfty.FTowerTripointed` |
| `D-2310` | section | `§ The genuine `Φ`-iterate tower` | `Dinfty.PhiIterateTower` |
| `D-2311` | section | `§ Tripointed ep-pairs between consecutive levels` | `Dinfty.PhiIterateTower` |
| `D-2312` | structure | `TriEP` | `Dinfty.PhiIterateTower` |
| `D-2313` | theorem | `prj_bot` | `Dinfty.PhiIterateTower` |
| `D-2314` | theorem | `prj_mid` | `Dinfty.PhiIterateTower` |
| `D-2315` | theorem | `prj_top` | `Dinfty.PhiIterateTower` |
| `D-2316` | section | `§ The two `End` actions` | `Dinfty.PhiIterateTower` |
| `D-2317` | def | `endUpFun` | `Dinfty.PhiIterateTower` |
| `D-2318` | theorem | `endUpFun_mono` | `Dinfty.PhiIterateTower` |
| `D-2319` | def | `endDownFun` | `Dinfty.PhiIterateTower` |
| `D-2320` | theorem | `endDownFun_mono` | `Dinfty.PhiIterateTower` |
| `D-2321` | def | `endUp` | `Dinfty.PhiIterateTower` |
| `D-2322` | def | `endDown` | `Dinfty.PhiIterateTower` |
| `D-2323` | section | `§ The two composites, before `Φ`` | `Dinfty.PhiIterateTower` |
| `D-2324` | theorem | `endDown_endUp` | `Dinfty.PhiIterateTower` |
| `D-2325` | theorem | `endUp_endDown_le` | `Dinfty.PhiIterateTower` |
| `D-2326` | section | `§ `Φ` is monotone in its morphism argument` | `Dinfty.PhiIterateTower` |
| `D-2327` | theorem | `phiTower_le_of_le` | `Dinfty.PhiIterateTower` |
| `D-2328` | theorem | `phiTower_congr` | `Dinfty.PhiIterateTower` |
| `D-2329` | section | `§ The step` | `Dinfty.PhiIterateTower` |
| `D-2330` | theorem | `step_retraction` | `Dinfty.PhiIterateTower` |
| `D-2331` | theorem | `step_deflation` | `Dinfty.PhiIterateTower` |
| `D-2332` | def | `phiStep` | `Dinfty.PhiIterateTower` |
| `D-2333` | section | `§ The base, and the tower` | `Dinfty.PhiIterateTower` |
| `D-2334` | def | `baseEP` | `Dinfty.PhiIterateTower` |
| `D-2335` | def | `iter` | `Dinfty.PhiIterateTower` |
| `D-2336` | def | `phiTowerEP` | `Dinfty.PhiIterateTower` |
| `D-2337` | theorem | `phiTowerEP_carrier` | `Dinfty.PhiIterateTower` |
| `D-2338` | theorem | `phiTowerEP_emb` | `Dinfty.PhiIterateTower` |
| `D-2339` | theorem | `emb_succ` | `Dinfty.PhiIterateTower` |
| `D-2340` | theorem | `prj_succ` | `Dinfty.PhiIterateTower` |
| `D-2341` | theorem | `emb_tripointed` | `Dinfty.PhiIterateTower` |
| `D-2342` | section | `§ The tower supplies the family: local continuity at the live `DBilimit`` | `Dinfty.DeflationContinuity` |
| `D-2343` | section | `§ The deflation family as a map` | `Dinfty.DeflationContinuity` |
| `D-2344` | def | `defl` | `Dinfty.DeflationContinuity` |
| `D-2345` | theorem | `defl_monotone` | `Dinfty.DeflationContinuity` |
| `D-2346` | def | `deflHom` | `Dinfty.DeflationContinuity` |
| `D-2347` | theorem | `deflHom_apply` | `Dinfty.DeflationContinuity` |
| `D-2348` | theorem | `proj_scottContinuous` | `Dinfty.DeflationContinuity` |
| `D-2349` | theorem | `insertAtLevel_scottContinuous` | `Dinfty.DeflationContinuity` |
| `D-2350` | theorem | `defl_scottContinuous` | `Dinfty.DeflationContinuity` |
| `D-2351` | theorem | `defl_isLUB` | `Dinfty.DeflationContinuity` |
| `D-2352` | theorem | `defl_directed` | `Dinfty.DeflationContinuity` |
| `D-2353` | section | `§ The `End` half, unconditionally, at the live tower` | `Dinfty.DeflationContinuity` |
| `D-2354` | theorem | `end_defl_isLUB` | `Dinfty.DeflationContinuity` |
| `D-2355` | section | `§ The same in `ScottEndP DBilimit`` | `Dinfty.DeflationContinuity` |
| `D-2356` | def | `endDefl` | `Dinfty.DeflationContinuity` |
| `D-2357` | theorem | `endDefl_apply` | `Dinfty.DeflationContinuity` |
| `D-2358` | theorem | `endDefl_isLUB` | `Dinfty.DeflationContinuity` |
| `D-2359` | section | `§ Why only copy `A`` | `Dinfty.DeflationContinuity` |
| `D-2360` | theorem | `defl_bot` | `Dinfty.DeflationContinuity` |
| `D-2361` | theorem | `endDefl_bot` | `Dinfty.DeflationContinuity` |
| `D-2362` | section | `§ Through `Φ`'s morphism action, at the live Ψ-target` | `Dinfty.DeflationContinuity` |
| `D-2363` | theorem | `psiTargetOrder_eq` | `Dinfty.DeflationContinuity` |
| `D-2364` | theorem | `phi_endDefl_isLUB` | `Dinfty.DeflationContinuity` |
| `D-2365` | section | `§ The live tower as an abstract ep-pair tower, and the deflation results made` | `Dinfty.RealEpPairTower` |
| `D-2366` | section | `§ The deflation family, abstractly` | `Dinfty.RealEpPairTower` |
| `D-2367` | def | `defl` | `Dinfty.RealEpPairTower` |
| `D-2368` | theorem | `defl_monotone` | `Dinfty.RealEpPairTower` |
| `D-2369` | theorem | `defl_range` | `Dinfty.RealEpPairTower` |
| `D-2370` | theorem | `defl_isLUB` | `Dinfty.RealEpPairTower` |
| `D-2371` | theorem | `defl_directed` | `Dinfty.RealEpPairTower` |
| `D-2372` | theorem | `proj_scottContinuous` | `Dinfty.RealEpPairTower` |
| `D-2373` | theorem | `ins_scottContinuous_of_finite` | `Dinfty.RealEpPairTower` |
| `D-2374` | theorem | `defl_scottContinuous` | `Dinfty.RealEpPairTower` |
| `D-2375` | theorem | `end_defl_isLUB` | `Dinfty.RealEpPairTower` |
| `D-2376` | section | `§ The live tower is one of these` | `Dinfty.RealEpPairTower` |
| `D-2377` | def | `realTower` | `Dinfty.RealEpPairTower` |
| `D-2378` | theorem | `realTower_carrier` | `Dinfty.RealEpPairTower` |
| `D-2379` | theorem | `realTower_prj` | `Dinfty.RealEpPairTower` |
| `D-2380` | theorem | `realTower_bilim` | `Dinfty.RealEpPairTower` |
| `D-2381` | instance | `realTower_finite` | `Dinfty.RealEpPairTower` |
| `D-2382` | theorem | `realTower_isDcpo` | `Dinfty.RealEpPairTower` |
| `D-2383` | theorem | `realTower_ins_scottContinuous` | `Dinfty.RealEpPairTower` |
| `D-2384` | theorem | `real_end_defl_isLUB` | `Dinfty.RealEpPairTower` |
| `D-2385` | section | `§ `D∞^Φ` — the Φ-iterate tower's bilimit, and `Φ` of it` | `Dinfty.PhiBilimit` |
| `D-2386` | abbrev | `B` | `Dinfty.PhiBilimit` |
| `D-2387` | section | `§ The three points assemble` | `Dinfty.PhiBilimit` |
| `D-2388` | def | `botB` | `Dinfty.PhiBilimit` |
| `D-2389` | def | `midB` | `Dinfty.PhiBilimit` |
| `D-2390` | def | `topB` | `Dinfty.PhiBilimit` |
| `D-2391` | theorem | `midB_apply` | `Dinfty.PhiBilimit` |
| `D-2392` | theorem | `botB_le` | `Dinfty.PhiBilimit` |
| `D-2393` | theorem | `le_topB` | `Dinfty.PhiBilimit` |
| `D-2394` | instance | `inst-OrderBot` | `Dinfty.PhiBilimit` |
| `D-2395` | instance | `inst-OrderTop` | `Dinfty.PhiBilimit` |
| `D-2396` | instance | `inst-BoundedOrder` | `Dinfty.PhiBilimit` |
| `D-2397` | theorem | `midB_ne_botB` | `Dinfty.PhiBilimit` |
| `D-2398` | theorem | `midB_ne_topB` | `Dinfty.PhiBilimit` |
| `D-2399` | theorem | `botB_ne_topB` | `Dinfty.PhiBilimit` |
| `D-2400` | section | `§ The staging maps are tripointed` | `Dinfty.PhiBilimit` |
| `D-2401` | theorem | `embLe_bot` | `Dinfty.PhiBilimit` |
| `D-2402` | theorem | `embLe_mid` | `Dinfty.PhiBilimit` |
| `D-2403` | theorem | `embLe_top` | `Dinfty.PhiBilimit` |
| `D-2404` | theorem | `prjLe_bot` | `Dinfty.PhiBilimit` |
| `D-2405` | theorem | `prjLe_mid` | `Dinfty.PhiBilimit` |
| `D-2406` | theorem | `prjLe_top` | `Dinfty.PhiBilimit` |
| `D-2407` | section | `§ …hence so is `ins`` | `Dinfty.PhiBilimit` |
| `D-2408` | theorem | `ins_bot` | `Dinfty.PhiBilimit` |
| `D-2409` | theorem | `ins_mid` | `Dinfty.PhiBilimit` |
| `D-2410` | theorem | `ins_top` | `Dinfty.PhiBilimit` |
| `D-2411` | theorem | `ins_tripointed` | `Dinfty.PhiBilimit` |
| `D-2412` | section | `§ `D∞^Φ` is directed-complete` | `Dinfty.PhiBilimit` |
| `D-2413` | instance | `finiteCarrier` | `Dinfty.PhiBilimit` |
| `D-2414` | theorem | `phiTowerEP_isDcpo` | `Dinfty.PhiBilimit` |
| `D-2415` | theorem | `ins_scottContinuous` | `Dinfty.PhiBilimit` |
| `D-2416` | theorem | `proj_scottContinuous` | `Dinfty.PhiBilimit` |
| `D-2417` | section | `§ `Φ(D∞^Φ)` is statable — over `ScottEndP`, not `EndP`` | `Dinfty.PhiBilimit` |
| `D-2418` | theorem | `scottContinuous_const` | `Dinfty.PhiBilimit` |
| `D-2419` | def | `constS` | `Dinfty.PhiBilimit` |
| `D-2420` | theorem | `constS_apply` | `Dinfty.PhiBilimit` |
| `D-2421` | instance | `inst-PartialOrder` | `Dinfty.PhiBilimit` |
| `D-2422` | theorem | `scottEndP_le_def` | `Dinfty.PhiBilimit` |
| `D-2423` | instance | `inst-OrderBot` | `Dinfty.PhiBilimit` |
| `D-2424` | instance | `inst-OrderTop` | `Dinfty.PhiBilimit` |
| `D-2425` | instance | `inst-BoundedOrder` | `Dinfty.PhiBilimit` |
| `D-2426` | instance | `decEqScottEndPB` | `Dinfty.PhiBilimit` |
| `D-2427` | def | `markedB` | `Dinfty.PhiBilimit` |
| `D-2428` | theorem | `markedB_ne_bot` | `Dinfty.PhiBilimit` |
| `D-2429` | theorem | `markedB_ne_top` | `Dinfty.PhiBilimit` |
| `D-2430` | theorem | `endPB_bot_ne_top` | `Dinfty.PhiBilimit` |
| `D-2431` | abbrev | `phiB` | `Dinfty.PhiBilimit` |
| `D-2432` | instance | `inst-PartialOrder` | `Dinfty.PhiBilimit` |
| `D-2433` | section | `§ `Φ` of the colimit cocone — rebuilt on values` | `Dinfty.PhiCocone` |
| `D-2434` | theorem | `hmk` | `Dinfty.PhiCocone` |
| `D-2435` | theorem | `hbtk` | `Dinfty.PhiCocone` |
| `D-2436` | section | `§ The tower's cocone, as tripointed morphisms of glue bases` | `Dinfty.PhiCocone` |
| `D-2437` | def | `insEndUp` | `Dinfty.PhiCocone` |
| `D-2438` | def | `projEndDown` | `Dinfty.PhiCocone` |
| `D-2439` | section | `§ The two composites, before `Φ`` | `Dinfty.PhiCocone` |
| `D-2440` | theorem | `projEndDown_insEndUp` | `Dinfty.PhiCocone` |
| `D-2441` | theorem | `insEndUp_projEndDown_le` | `Dinfty.PhiCocone` |
| `D-2442` | theorem | `insEndUp_comp_emb` | `Dinfty.PhiCocone` |
| `D-2443` | section | `§ The legs, built on values` | `Dinfty.PhiCocone` |
| `D-2444` | def | `eLeg` | `Dinfty.PhiCocone` |
| `D-2445` | def | `pLeg` | `Dinfty.PhiCocone` |
| `D-2446` | theorem | `eLeg_monotone` | `Dinfty.PhiCocone` |
| `D-2447` | theorem | `pLeg_monotone` | `Dinfty.PhiCocone` |
| `D-2448` | section | `§ Three of the four `IsColimitCocone` fields` | `Dinfty.PhiCocone` |
| `D-2449` | theorem | `cocone_retraction` | `Dinfty.PhiCocone` |
| `D-2450` | theorem | `cocone_deflation` | `Dinfty.PhiCocone` |
| `D-2451` | theorem | `cocone_compat` | `Dinfty.PhiCocone` |
| `D-2452` | section | `§ The remaining obligations, named` | `Dinfty.PhiCocone` |
| `D-2453` | def | `PhiCoconeIsLUB` | `Dinfty.PhiCocone` |
| `D-2454` | def | `PhiSupExists` | `Dinfty.PhiCocone` |
| `D-2455` | def | `PhiProjContinuous` | `Dinfty.PhiCocone` |
| `D-2456` | theorem | `isColimitCocone` | `Dinfty.PhiCocone` |
| `D-2457` | def | `theoremA_orderIso` | `Dinfty.PhiCocone` |
| `D-2458` | section | `§ Chain suprema in `D∞^Φ` and in `ScottEndP (D∞^Φ)`` | `Dinfty.PhiChainSup` |
| `D-2459` | section | `§ Monotone `ℕ`-families` | `Dinfty.PhiChainSup` |
| `D-2460` | theorem | `range_nonempty` | `Dinfty.PhiChainSup` |
| `D-2461` | theorem | `range_directedOn` | `Dinfty.PhiChainSup` |
| `D-2462` | theorem | `exists_eventually_const` | `Dinfty.PhiChainSup` |
| `D-2463` | section | `§ `B` has the suprema of chains` | `Dinfty.PhiChainSup` |
| `D-2464` | theorem | `exists_chain_lub` | `Dinfty.PhiChainSup` |
| `D-2465` | section | `§ …and so does `ScottEndP B`, pointwise` | `Dinfty.PhiChainSup` |
| `D-2466` | theorem | `ptwise_mono` | `Dinfty.PhiChainSup` |
| `D-2467` | theorem | `ptwise_ex` | `Dinfty.PhiChainSup` |
| `D-2468` | def | `supFun` | `Dinfty.PhiChainSup` |
| `D-2469` | theorem | `supFun_isLUB` | `Dinfty.PhiChainSup` |
| `D-2470` | theorem | `supFun_mono` | `Dinfty.PhiChainSup` |
| `D-2471` | theorem | `supFun_scott` | `Dinfty.PhiChainSup` |
| `D-2472` | def | `chainSup` | `Dinfty.PhiChainSup` |
| `D-2473` | theorem | `chainSup_apply` | `Dinfty.PhiChainSup` |
| `D-2474` | theorem | `chainSup_isLUB` | `Dinfty.PhiChainSup` |
| `D-2475` | section | `§ The projection legs carry those suprema` | `Dinfty.PhiChainSup` |
| `D-2476` | theorem | `projEndDown_isLUB` | `Dinfty.PhiChainSup` |
| `D-2477` | section | `§ The analysis: `⨆ₖ Φ(δₖ) = id` on `Φ(D∞^Φ)`` | `Dinfty.PhiCoconeLUB` |
| `D-2478` | theorem | `hmk` | `Dinfty.PhiCoconeLUB` |
| `D-2479` | section | `§ Two facts about monotone `ℕ`-families` | `Dinfty.PhiCoconeLUB` |
| `D-2480` | theorem | `eventually_ne_of_isLUB` | `Dinfty.PhiCoconeLUB` |
| `D-2481` | theorem | `isLUB_tail` | `Dinfty.PhiCoconeLUB` |
| `D-2482` | section | `§ The deflations of `B`, and `⨆ₖ δₖ ∘ h ∘ δₖ = h`` | `Dinfty.PhiCoconeLUB` |
| `D-2483` | def | `defl` | `Dinfty.PhiCoconeLUB` |
| `D-2484` | theorem | `defl_scott` | `Dinfty.PhiCoconeLUB` |
| `D-2485` | theorem | `defl_index_mono` | `Dinfty.PhiCoconeLUB` |
| `D-2486` | theorem | `defl_dir` | `Dinfty.PhiCoconeLUB` |
| `D-2487` | theorem | `defl_lub` | `Dinfty.PhiCoconeLUB` |
| `D-2488` | theorem | `end_defl_isLUB` | `Dinfty.PhiCoconeLUB` |
| `D-2489` | section | `§ The same in `ScottEndP B` — the map `Φ` is applied to` | `Dinfty.PhiCoconeLUB` |
| `D-2490` | def | `bigDelta` | `Dinfty.PhiCoconeLUB` |
| `D-2491` | theorem | `bigDelta_apply` | `Dinfty.PhiCoconeLUB` |
| `D-2492` | theorem | `bigDelta_isLUB` | `Dinfty.PhiCoconeLUB` |
| `D-2493` | theorem | `bigDelta_mono` | `Dinfty.PhiCoconeLUB` |
| `D-2494` | section | `§ Through the glue` | `Dinfty.PhiCoconeLUB` |
| `D-2495` | theorem | `eLeg_pLeg_val` | `Dinfty.PhiCoconeLUB` |
| `D-2496` | theorem | `least_of_tail` | `Dinfty.PhiCoconeLUB` |
| `D-2497` | section | `§ The theorem` | `Dinfty.PhiCoconeLUB` |
| `D-2498` | theorem | `phiCoconeIsLUB` | `Dinfty.PhiCoconeLUB` |
| `D-2499` | section | `§ What is now unconditional` | `Dinfty.PhiCoconeLUB` |
| `D-2500` | theorem | `isColimitCocone` | `Dinfty.PhiCoconeLUB` |
| `D-2501` | theorem | `hpm` | `Dinfty.PhiCoconeLUB` |
| `D-2502` | theorem | `hem` | `Dinfty.PhiCoconeLUB` |
| `D-2503` | def | `toShiftBilim` | `Dinfty.PhiCoconeLUB` |
| `D-2504` | theorem | `toShiftBilim_le_iff` | `Dinfty.PhiCoconeLUB` |
| `D-2505` | theorem | `toShiftBilim_injective` | `Dinfty.PhiCoconeLUB` |
| `D-2506` | def | `theoremA_orderIso` | `Dinfty.PhiCoconeLUB` |
| `D-2507` | section | `§ Surjectivity: `PhiSupExists` and `PhiProjContinuous`` | `Dinfty.PhiSurjective` |
| `D-2508` | theorem | `hmk` | `Dinfty.PhiSurjective` |
| `D-2509` | theorem | `hbtk` | `Dinfty.PhiSurjective` |
| `D-2510` | theorem | `hpm` | `Dinfty.PhiSurjective` |
| `D-2511` | theorem | `hem` | `Dinfty.PhiSurjective` |
| `D-2512` | section | `§ Two small generalities` | `Dinfty.PhiSurjective` |
| `D-2513` | theorem | `isLUB_of_tail` | `Dinfty.PhiSurjective` |
| `D-2514` | theorem | `endUp_endDown_le` | `Dinfty.PhiSurjective` |
| `D-2515` | section | `§ The tower's projection, on values` | `Dinfty.PhiSurjective` |
| `D-2516` | theorem | `prj_succ` | `Dinfty.PhiSurjective` |
| `D-2517` | theorem | `d_val` | `Dinfty.PhiSurjective` |
| `D-2518` | section | `§ `pLeg` on tag points` | `Dinfty.PhiSurjective` |
| `D-2519` | theorem | `pLeg_tagPt` | `Dinfty.PhiSurjective` |
| `D-2520` | section | `§ `insEndUp` is injective, and carries the canon-fixed condition` | `Dinfty.PhiSurjective` |
| `D-2521` | theorem | `insEndUp_retract` | `Dinfty.PhiSurjective` |
| `D-2522` | theorem | `insEndUp_injective` | `Dinfty.PhiSurjective` |
| `D-2523` | theorem | `fix_transport` | `Dinfty.PhiSurjective` |
| `D-2524` | section | `§ The legs read the tower back` | `Dinfty.PhiSurjective` |
| `D-2525` | theorem | `himg_ge` | `Dinfty.PhiSurjective` |
| `D-2526` | section | `§ The chain, and its tag` | `Dinfty.PhiSurjective` |
| `D-2527` | theorem | `chain_mono` | `Dinfty.PhiSurjective` |
| `D-2528` | theorem | `tag_mono` | `Dinfty.PhiSurjective` |
| `D-2529` | section | `§ The construction` | `Dinfty.PhiSurjective` |
| `D-2530` | theorem | `exists_lub_with_proj` | `Dinfty.PhiSurjective` |
| `D-2531` | section | `§ The two hypotheses, and Theorem A's order-theoretic half` | `Dinfty.PhiSurjective` |
| `D-2532` | theorem | `phiSupExists` | `Dinfty.PhiSurjective` |
| `D-2533` | theorem | `phiProjContinuous` | `Dinfty.PhiSurjective` |
| `D-2534` | def | `theoremA_orderIso` | `Dinfty.PhiSurjective` |
| `D-2535` | section | `§ The honest internal IFS on `D∞^Φ`` | `Dinfty.InternalIFSInstance` |
| `D-2536` | def | `sec` | `Dinfty.InternalIFSInstance` |
| `D-2537` | theorem | `sec_injective` | `Dinfty.InternalIFSInstance` |
| `D-2538` | theorem | `sec_surjective` | `Dinfty.InternalIFSInstance` |
| `D-2539` | section | `§ Two small injectivity inputs` | `Dinfty.InternalIFSInstance` |
| `D-2540` | theorem | `constS_injective` | `Dinfty.InternalIFSInstance` |
| `D-2541` | theorem | `constS_bot` | `Dinfty.InternalIFSInstance` |
| `D-2542` | section | `§ The glue bottom` | `Dinfty.InternalIFSInstance` |
| `D-2543` | theorem | `tagA_bot_le_raw` | `Dinfty.InternalIFSInstance` |
| `D-2544` | theorem | `tagA_bot_le` | `Dinfty.InternalIFSInstance` |
| `D-2545` | section | `§ The internal IFS` | `Dinfty.InternalIFSInstance` |
| `D-2546` | def | `ifsB` | `Dinfty.InternalIFSInstance` |
| `D-2547` | theorem | `sigmaA_apply` | `Dinfty.InternalIFSInstance` |
| `D-2548` | theorem | `sigmaB_apply` | `Dinfty.InternalIFSInstance` |
| `D-2549` | theorem | `sigmaC_apply` | `Dinfty.InternalIFSInstance` |
| `D-2550` | section | `§ Injectivity — on all of `B`, for all three copies` | `Dinfty.InternalIFSInstance` |
| `D-2551` | theorem | `sigma_inj` | `Dinfty.InternalIFSInstance` |
| `D-2552` | theorem | `sigmaA_injective` | `Dinfty.InternalIFSInstance` |
| `D-2553` | theorem | `sigmaB_injective` | `Dinfty.InternalIFSInstance` |
| `D-2554` | theorem | `sigmaC_injective` | `Dinfty.InternalIFSInstance` |
| `D-2555` | section | `§ `⊥` is fixed by copy `A`` | `Dinfty.InternalIFSInstance` |
| `D-2556` | theorem | `sigmaA_bot` | `Dinfty.InternalIFSInstance` |
| `D-2557` | theorem | `bot_mem_fix_sigmaA` | `Dinfty.InternalIFSInstance` |
| `D-2558` | section | `§ `sec`'s coordinates are the projection legs` | `Dinfty.InternalIFSInstance` |
| `D-2559` | theorem | `sec_apply_succ` | `Dinfty.InternalIFSInstance` |
| `D-2560` | theorem | `sec_apply_zero` | `Dinfty.InternalIFSInstance` |
| `D-2561` | theorem | `projEndDown_markedB` | `Dinfty.InternalIFSInstance` |
| `D-2562` | theorem | `pLeg_val` | `Dinfty.InternalIFSInstance` |
| `D-2563` | section | `§ Self-similarity, named` | `Dinfty.InternalIFSInstance` |
| `D-2564` | theorem | `selfSimilar` | `Dinfty.InternalIFSInstance` |
| `D-2565` | section | `§ Rebuilding `σ`, and a correction about what ESCAPE was needed for` | `Dinfty.SigmaRebuild` |
| `D-2566` | section | `§ The correction, stated and proved` | `Dinfty.SigmaRebuild` |
| `D-2567` | theorem | `base_pin_of_mem` | `Dinfty.SigmaRebuild` |
| `D-2568` | theorem | `theoremA_unique_of_mem` | `Dinfty.SigmaRebuild` |
| `D-2569` | section | `§ The strict constant` | `Dinfty.SigmaRebuild` |
| `D-2570` | def | `strictFun` | `Dinfty.SigmaRebuild` |
| `D-2571` | theorem | `strictFun_bot_case` | `Dinfty.SigmaRebuild` |
| `D-2572` | theorem | `strictFun_ne_case` | `Dinfty.SigmaRebuild` |
| `D-2573` | theorem | `strictFun_mono` | `Dinfty.SigmaRebuild` |
| `D-2574` | theorem | `strictFun_scott` | `Dinfty.SigmaRebuild` |
| `D-2575` | def | `strictConst` | `Dinfty.SigmaRebuild` |
| `D-2576` | theorem | `strictConst_apply` | `Dinfty.SigmaRebuild` |
| `D-2577` | theorem | `topB_ne_bot` | `Dinfty.SigmaRebuild` |
| `D-2578` | theorem | `strictConst_injective` | `Dinfty.SigmaRebuild` |
| `D-2579` | theorem | `strictConst_bot` | `Dinfty.SigmaRebuild` |
| `D-2580` | section | `§ The rebuilt internal IFS` | `Dinfty.SigmaRebuild` |
| `D-2581` | def | `ifsS` | `Dinfty.SigmaRebuild` |
| `D-2582` | theorem | `sigmaS_inj` | `Dinfty.SigmaRebuild` |
| `D-2583` | theorem | `sigmaA_injective` | `Dinfty.SigmaRebuild` |
| `D-2584` | theorem | `sigmaB_injective` | `Dinfty.SigmaRebuild` |
| `D-2585` | theorem | `sigmaC_injective` | `Dinfty.SigmaRebuild` |
| `D-2586` | section | `§ `⊥` is still fixed, and the marked point is not` | `Dinfty.SigmaRebuild` |
| `D-2587` | theorem | `sigmaA_bot` | `Dinfty.SigmaRebuild` |
| `D-2588` | theorem | `bot_mem_fix` | `Dinfty.SigmaRebuild` |
| `D-2589` | theorem | `sigmaA_mid_ne` | `Dinfty.SigmaRebuild` |
| `D-2590` | theorem | `mid_not_mem_fix` | `Dinfty.SigmaRebuild` |
| `D-2591` | section | `§ `qAA` explicitly — and a retraction` | `Dinfty.QAAExplicit` |
| `D-2592` | section | `§ `qAA` is a definition, not a choice` | `Dinfty.QAAExplicit` |
| `D-2593` | theorem | `qAA_eq` | `Dinfty.QAAExplicit` |
| `D-2594` | theorem | `glueAA_qAA_le` | `Dinfty.QAAExplicit` |
| `D-2595` | theorem | `le_qAA` | `Dinfty.QAAExplicit` |
| `D-2596` | theorem | `qAA_isGreatest` | `Dinfty.QAAExplicit` |
| `D-2597` | theorem | `eq_qAA_of_isGreatest` | `Dinfty.QAAExplicit` |
| `D-2598` | theorem | `glueAA_le_iff_le_qAA` | `Dinfty.QAAExplicit` |
| `D-2599` | section | `§ The tower's base projection *is* this map` | `Dinfty.QAAExplicit` |
| `D-2600` | theorem | `prj_zero_eq` | `Dinfty.QAAExplicit` |
| `D-2601` | theorem | `level_zero_isGreatest` | `Dinfty.QAAExplicit` |
| `D-2602` | section | `§ The payload of a strict constant, pinned` | `Dinfty.QAAExplicit` |
| `D-2603` | theorem | `ins_eq_bot_iff` | `Dinfty.QAAExplicit` |
| `D-2604` | theorem | `projEndDown_strictConst_bot` | `Dinfty.QAAExplicit` |
| `D-2605` | theorem | `projEndDown_strictConst_ne` | `Dinfty.QAAExplicit` |
| `D-2606` | section | `§ The base equation for a fixed point of the rebuilt `σ_A`, with nothing` | `Dinfty.QAAExplicit` |
| `D-2607` | theorem | `fix_level_one` | `Dinfty.QAAExplicit` |
| `D-2608` | theorem | `fix_level_zero` | `Dinfty.QAAExplicit` |
| `D-2609` | section | `§ Theorem ESCAPE holds for the rebuilt `σ_A`` | `Dinfty.EscapeProof` |
| `D-2610` | section | `§ Small facts about the tower's copy-`A` inclusion` | `Dinfty.EscapeProof` |
| `D-2611` | theorem | `botD_val` | `Dinfty.EscapeProof` |
| `D-2612` | theorem | `iotaD_eq_bot_iff` | `Dinfty.EscapeProof` |
| `D-2613` | theorem | `dMid_le_of_not_tagA` | `Dinfty.EscapeProof` |
| `D-2614` | section | `§ The key inequality` | `Dinfty.EscapeProof` |
| `D-2615` | theorem | `eq_bot_of_glueAA_le` | `Dinfty.EscapeProof` |
| `D-2616` | section | `§ …and the theorem` | `Dinfty.EscapeProof` |
| `D-2617` | theorem | `fix_level_succ` | `Dinfty.EscapeProof` |
| `D-2618` | theorem | `level_zero_eq_bot` | `Dinfty.EscapeProof` |
| `D-2619` | theorem | `eq_bot_of_fix` | `Dinfty.EscapeProof` |
| `D-2620` | theorem | `fix_sigmaA` | `Dinfty.EscapeProof` |
| `D-2621` | section | `§ `Γ` — the Sierpiński gasket, as an actual attractor` | `Dinfty.Gasket` |
| `D-2622` | section | `§ 1.  A Lipschitz map is Lipschitz on nonempty compacts` | `Dinfty.Gasket` |
| `D-2623` | theorem | `infEDist_image_le` | `Dinfty.Gasket` |
| `D-2624` | theorem | `hausdorffEDist_image_le` | `Dinfty.Gasket` |
| `D-2625` | theorem | `lipschitzWith_map` | `Dinfty.Gasket` |
| `D-2626` | section | `§ 2.  The three contractions` | `Dinfty.Gasket` |
| `D-2627` | abbrev | `E` | `Dinfty.Gasket` |
| `D-2628` | def | `cA` | `Dinfty.Gasket` |
| `D-2629` | def | `cB` | `Dinfty.Gasket` |
| `D-2630` | def | `cC` | `Dinfty.Gasket` |
| `D-2631` | def | `vA` | `Dinfty.Gasket` |
| `D-2632` | def | `vB` | `Dinfty.Gasket` |
| `D-2633` | def | `vC` | `Dinfty.Gasket` |
| `D-2634` | def | `contract` | `Dinfty.Gasket` |
| `D-2635` | theorem | `contract_lipschitz` | `Dinfty.Gasket` |
| `D-2636` | theorem | `contract_continuous` | `Dinfty.Gasket` |
| `D-2637` | theorem | `contract_vA` | `Dinfty.Gasket` |
| `D-2638` | theorem | `contract_vB` | `Dinfty.Gasket` |
| `D-2639` | theorem | `contract_vC` | `Dinfty.Gasket` |
| `D-2640` | section | `§ 3.  The Hutchinson operator and its fixed point` | `Dinfty.Gasket` |
| `D-2641` | def | `hutch` | `Dinfty.Gasket` |
| `D-2642` | theorem | `coe_hutch` | `Dinfty.Gasket` |
| `D-2643` | theorem | `hutch_lipschitz` | `Dinfty.Gasket` |
| `D-2644` | theorem | `hutch_contracting` | `Dinfty.Gasket` |
| `D-2645` | theorem | `edist_ne_top` | `Dinfty.Gasket` |
| `D-2646` | def | `gasketNC` | `Dinfty.Gasket` |
| `D-2647` | theorem | `hutch_gasketNC` | `Dinfty.Gasket` |
| `D-2648` | def | `gasketSet` | `Dinfty.Gasket` |
| `D-2649` | theorem | `gasketSet_nonempty` | `Dinfty.Gasket` |
| `D-2650` | theorem | `isCompact_gasketSet` | `Dinfty.Gasket` |
| `D-2651` | theorem | `gasketSet_eq` | `Dinfty.Gasket` |
| `D-2652` | theorem | `mapsTo_cA` | `Dinfty.Gasket` |
| `D-2653` | theorem | `mapsTo_cB` | `Dinfty.Gasket` |
| `D-2654` | theorem | `mapsTo_cC` | `Dinfty.Gasket` |
| `D-2655` | section | `§ 4.  `Γ` as a compact metric space, with its three maps` | `Dinfty.Gasket` |
| `D-2656` | abbrev | `Gamma` | `Dinfty.Gasket` |
| `D-2657` | instance | `inst-CompactSpace` | `Dinfty.Gasket` |
| `D-2658` | instance | `inst-Nonempty` | `Dinfty.Gasket` |
| `D-2659` | def | `fA` | `Dinfty.Gasket` |
| `D-2660` | def | `fB` | `Dinfty.Gasket` |
| `D-2661` | def | `fC` | `Dinfty.Gasket` |
| `D-2662` | theorem | `continuous_fA` | `Dinfty.Gasket` |
| `D-2663` | theorem | `continuous_fB` | `Dinfty.Gasket` |
| `D-2664` | theorem | `continuous_fC` | `Dinfty.Gasket` |
| `D-2665` | section | `§ 5.  The three vertices lie in `Γ`, and are distinct` | `Dinfty.Gasket` |
| `D-2666` | theorem | `dist_iterate_le` | `Dinfty.Gasket` |
| `D-2667` | theorem | `fixedPoint_mem_gasketSet` | `Dinfty.Gasket` |
| `D-2668` | theorem | `vA_mem` | `Dinfty.Gasket` |
| `D-2669` | theorem | `vB_mem` | `Dinfty.Gasket` |
| `D-2670` | theorem | `vC_mem` | `Dinfty.Gasket` |
| `D-2671` | theorem | `vA_ne_vB` | `Dinfty.Gasket` |
| `D-2672` | theorem | `vA_ne_vC` | `Dinfty.Gasket` |
| `D-2673` | theorem | `vB_ne_vC` | `Dinfty.Gasket` |
| `D-2674` | section | `§ …as points of `Γ`` | `Dinfty.Gasket` |
| `D-2675` | def | `gA` | `Dinfty.Gasket` |
| `D-2676` | def | `gB` | `Dinfty.Gasket` |
| `D-2677` | def | `gC` | `Dinfty.Gasket` |
| `D-2678` | theorem | `fA_gA` | `Dinfty.Gasket` |
| `D-2679` | theorem | `fB_gB` | `Dinfty.Gasket` |
| `D-2680` | theorem | `fC_gC` | `Dinfty.Gasket` |
| `D-2681` | theorem | `gA_ne_gB` | `Dinfty.Gasket` |
| `D-2682` | theorem | `gA_ne_gC` | `Dinfty.Gasket` |
| `D-2683` | theorem | `gB_ne_gC` | `Dinfty.Gasket` |
| `D-2684` | theorem | `gamma_nontrivial` | `Dinfty.Gasket` |
| `D-2685` | section | `§ The coding map `π : {A,B,C}^ℕ ↠ Γ`` | `Dinfty.GasketCoding` |
| `D-2686` | section | `§ 1.  The three maps, indexed` | `Dinfty.GasketCoding` |
| `D-2687` | def | `cw` | `Dinfty.GasketCoding` |
| `D-2688` | def | `step` | `Dinfty.GasketCoding` |
| `D-2689` | theorem | `step_lipschitz` | `Dinfty.GasketCoding` |
| `D-2690` | theorem | `step_continuous` | `Dinfty.GasketCoding` |
| `D-2691` | theorem | `step_mapsTo` | `Dinfty.GasketCoding` |
| `D-2692` | theorem | `dist_step_vA_le` | `Dinfty.GasketCoding` |
| `D-2693` | section | `§ 2.  Prefix maps` | `Dinfty.GasketCoding` |
| `D-2694` | def | `pre` | `Dinfty.GasketCoding` |
| `D-2695` | theorem | `pre_zero` | `Dinfty.GasketCoding` |
| `D-2696` | theorem | `pre_succ` | `Dinfty.GasketCoding` |
| `D-2697` | theorem | `pre_lipschitz` | `Dinfty.GasketCoding` |
| `D-2698` | theorem | `pre_mapsTo` | `Dinfty.GasketCoding` |
| `D-2699` | theorem | `pre_congr` | `Dinfty.GasketCoding` |
| `D-2700` | section | `§ 3.  The approximating sequence and its limit` | `Dinfty.GasketCoding` |
| `D-2701` | def | `xseq` | `Dinfty.GasketCoding` |
| `D-2702` | theorem | `xseq_mem` | `Dinfty.GasketCoding` |
| `D-2703` | theorem | `dist_xseq_succ` | `Dinfty.GasketCoding` |
| `D-2704` | theorem | `xseq_cauchy` | `Dinfty.GasketCoding` |
| `D-2705` | def | `coding` | `Dinfty.GasketCoding` |
| `D-2706` | theorem | `coding_tendsto` | `Dinfty.GasketCoding` |
| `D-2707` | theorem | `coding_mem` | `Dinfty.GasketCoding` |
| `D-2708` | theorem | `dist_xseq_coding` | `Dinfty.GasketCoding` |
| `D-2709` | theorem | `dist_vA_coding` | `Dinfty.GasketCoding` |
| `D-2710` | section | `§ 4.  Equivariance` | `Dinfty.GasketCoding` |
| `D-2711` | def | `cons` | `Dinfty.GasketCoding` |
| `D-2712` | theorem | `pre_cons` | `Dinfty.GasketCoding` |
| `D-2713` | theorem | `xseq_cons` | `Dinfty.GasketCoding` |
| `D-2714` | theorem | `coding_cons` | `Dinfty.GasketCoding` |
| `D-2715` | section | `§ 5.  Surjectivity` | `Dinfty.GasketCoding` |
| `D-2716` | theorem | `exists_pred` | `Dinfty.GasketCoding` |
| `D-2717` | def | `peel` | `Dinfty.GasketCoding` |
| `D-2718` | theorem | `peel_spec` | `Dinfty.GasketCoding` |
| `D-2719` | def | `orbit` | `Dinfty.GasketCoding` |
| `D-2720` | def | `addr` | `Dinfty.GasketCoding` |
| `D-2721` | theorem | `orbit_step` | `Dinfty.GasketCoding` |
| `D-2722` | theorem | `pre_orbit` | `Dinfty.GasketCoding` |
| `D-2723` | theorem | `dist_xseq_addr` | `Dinfty.GasketCoding` |
| `D-2724` | theorem | `coding_surjOn` | `Dinfty.GasketCoding` |
| `D-2725` | theorem | `gasketSet_subset_closedBall` | `Dinfty.GasketCoding` |
| `D-2726` | section | `§ 6.  Continuity` | `Dinfty.GasketCoding` |
| `D-2727` | theorem | `coding_eq_of_prefix` | `Dinfty.GasketCoding` |
| `D-2728` | theorem | `dist_coding_le_of_prefix` | `Dinfty.GasketCoding` |
| `D-2729` | theorem | `continuous_coding` | `Dinfty.GasketCoding` |
| `D-2730` | section | `§ 7.  …valued in `Γ`` | `Dinfty.GasketCoding` |
| `D-2731` | def | `codeGamma` | `Dinfty.GasketCoding` |
| `D-2732` | theorem | `continuous_codeGamma` | `Dinfty.GasketCoding` |
| `D-2733` | theorem | `codeGamma_surjective` | `Dinfty.GasketCoding` |
| `D-2734` | theorem | `codeGamma_cons_zero` | `Dinfty.GasketCoding` |
| `D-2735` | theorem | `codeGamma_cons_one` | `Dinfty.GasketCoding` |
| `D-2736` | theorem | `codeGamma_cons_two` | `Dinfty.GasketCoding` |
| `D-2737` | section | `§ The address space as a `CoreIFS` over the real `Γ`` | `Dinfty.GasketCoreIFS` |
| `D-2738` | section | `§ 1.  The shift` | `Dinfty.GasketCoreIFS` |
| `D-2739` | def | `tail` | `Dinfty.GasketCoreIFS` |
| `D-2740` | theorem | `tail_iterate` | `Dinfty.GasketCoreIFS` |
| `D-2741` | theorem | `cons_head_tail` | `Dinfty.GasketCoreIFS` |
| `D-2742` | section | `§ 2.  Equivariance pins the map — with no continuity hypothesis` | `Dinfty.GasketCoreIFS` |
| `D-2743` | theorem | `step_head` | `Dinfty.GasketCoreIFS` |
| `D-2744` | theorem | `pre_iterate_eq` | `Dinfty.GasketCoreIFS` |
| `D-2745` | theorem | `coding_unique` | `Dinfty.GasketCoreIFS` |
| `D-2746` | section | `§ 3.  `π` is a quotient map — but not an open one` | `Dinfty.GasketCoreIFS` |
| `D-2747` | instance | `inst-CompactSpace` | `Dinfty.GasketCoreIFS` |
| `D-2748` | theorem | `isClosedMap_codeGamma` | `Dinfty.GasketCoreIFS` |
| `D-2749` | theorem | `isQuotientMap_codeGamma` | `Dinfty.GasketCoreIFS` |
| `D-2750` | section | `§ 4.  The `CoreIFS` data` | `Dinfty.GasketCoreIFS` |
| `D-2751` | def | `addressCoreIFS` | `Dinfty.GasketCoreIFS` |
| `D-2752` | theorem | `addressCoreIFS_equivariant` | `Dinfty.GasketCoreIFS` |
| `D-2753` | theorem | `addressCoreIFS_unique` | `Dinfty.GasketCoreIFS` |
| `D-2754` | section | `§ `TheoremAData.quotient_map` asks for something false` | `Dinfty.GasketNotOpen` |
| `D-2755` | section | `§ 1.  Coordinates on the gasket` | `Dinfty.GasketNotOpen` |
| `D-2756` | theorem | `fst_le_one` | `Dinfty.GasketNotOpen` |
| `D-2757` | theorem | `contract_cA_fst` | `Dinfty.GasketNotOpen` |
| `D-2758` | theorem | `contract_cB_fst` | `Dinfty.GasketNotOpen` |
| `D-2759` | theorem | `fst_le_half_of_mem_imageA` | `Dinfty.GasketNotOpen` |
| `D-2760` | section | `§ 2.  The contact point, and points of `Γ` approaching it from the `B` side` | `Dinfty.GasketNotOpen` |
| `D-2761` | def | `mid` | `Dinfty.GasketNotOpen` |
| `D-2762` | theorem | `mid_mem_imageA` | `Dinfty.GasketNotOpen` |
| `D-2763` | theorem | `mid_mem` | `Dinfty.GasketNotOpen` |
| `D-2764` | theorem | `mid_eq` | `Dinfty.GasketNotOpen` |
| `D-2765` | def | `qq` | `Dinfty.GasketNotOpen` |
| `D-2766` | theorem | `qq_mem` | `Dinfty.GasketNotOpen` |
| `D-2767` | theorem | `qq_eq` | `Dinfty.GasketNotOpen` |
| `D-2768` | def | `pp` | `Dinfty.GasketNotOpen` |
| `D-2769` | theorem | `pp_mem` | `Dinfty.GasketNotOpen` |
| `D-2770` | theorem | `pp_eq` | `Dinfty.GasketNotOpen` |
| `D-2771` | theorem | `pp_not_mem_imageA` | `Dinfty.GasketNotOpen` |
| `D-2772` | theorem | `dist_pp_mid` | `Dinfty.GasketNotOpen` |
| `D-2773` | section | `§ 3.  The `A`-copy is not open in `Γ`` | `Dinfty.GasketNotOpen` |
| `D-2774` | theorem | `not_isOpen_imageA` | `Dinfty.GasketNotOpen` |
| `D-2775` | section | `§ 4.  …hence `π` is not an open map` | `Dinfty.GasketNotOpen` |
| `D-2776` | theorem | `image_cylinder` | `Dinfty.GasketNotOpen` |
| `D-2777` | theorem | `isOpen_cylinder` | `Dinfty.GasketNotOpen` |
| `D-2778` | theorem | `notOpen` | `Dinfty.GasketNotOpen` |
| `D-2779` | section | `§ What `Γ` forces on any internal IFS` | `Dinfty.GasketObstruction` |
| `D-2780` | section | `§ 1.  A contraction has at most one fixed point` | `Dinfty.GasketObstruction` |
| `D-2781` | theorem | `eq_of_contract_fixed` | `Dinfty.GasketObstruction` |
| `D-2782` | theorem | `fA_fixed_unique` | `Dinfty.GasketObstruction` |
| `D-2783` | theorem | `fB_fixed_unique` | `Dinfty.GasketObstruction` |
| `D-2784` | theorem | `fC_fixed_unique` | `Dinfty.GasketObstruction` |
| `D-2785` | section | `§ 2.  Equivariance is constant on fixed-point sets` | `Dinfty.GasketObstruction` |
| `D-2786` | theorem | `rho_eq_gA` | `Dinfty.GasketObstruction` |
| `D-2787` | theorem | `rho_eq_gB` | `Dinfty.GasketObstruction` |
| `D-2788` | theorem | `rho_eq_gC` | `Dinfty.GasketObstruction` |
| `D-2789` | theorem | `no_shared_fix_AB` | `Dinfty.GasketObstruction` |
| `D-2790` | theorem | `no_shared_fix_AC` | `Dinfty.GasketObstruction` |
| `D-2791` | theorem | `no_shared_fix_BC` | `Dinfty.GasketObstruction` |
| `D-2792` | section | `§ 3.  Running the test on `SigmaRebuild.ifsS`` | `Dinfty.GasketObstruction` |
| `D-2793` | theorem | `tagB_bot_eq_mark` | `Dinfty.GasketObstruction` |
| `D-2794` | theorem | `tagC_bot_eq_top` | `Dinfty.GasketObstruction` |
| `D-2795` | theorem | `sec_tagA_bot` | `Dinfty.GasketObstruction` |
| `D-2796` | theorem | `ifsS_sigmaB_bot` | `Dinfty.GasketObstruction` |
| `D-2797` | theorem | `ifsS_sigmaC_bot` | `Dinfty.GasketObstruction` |
| `D-2798` | theorem | `ifsS_sigmaB_bot_ne` | `Dinfty.GasketObstruction` |
| `D-2799` | theorem | `ifsS_sigmaC_bot_ne` | `Dinfty.GasketObstruction` |
| `D-2800` | theorem | `bot_not_mem_fix_B` | `Dinfty.GasketObstruction` |
| `D-2801` | theorem | `bot_not_mem_fix_C` | `Dinfty.GasketObstruction` |
| `D-2802` | theorem | `ifsS_fix_disjoint_AB` | `Dinfty.GasketObstruction` |
| `D-2803` | theorem | `ifsS_fix_disjoint_AC` | `Dinfty.GasketObstruction` |
| `D-2804` | theorem | `rho_bot` | `Dinfty.GasketObstruction` |
| `D-2805` | section | `§ The address map into `B`` | `Dinfty.CodeB` |
| `D-2806` | section | `§ 1.  The three maps, indexed` | `Dinfty.CodeB` |
| `D-2807` | def | `sig` | `Dinfty.CodeB` |
| `D-2808` | theorem | `sig_zero` | `Dinfty.CodeB` |
| `D-2809` | theorem | `sig_one` | `Dinfty.CodeB` |
| `D-2810` | theorem | `sig_two` | `Dinfty.CodeB` |
| `D-2811` | theorem | `fin3_cases` | `Dinfty.CodeB` |
| `D-2812` | theorem | `tag_le_two` | `Dinfty.CodeB` |
| `D-2813` | section | `§ 2.  The payload` | `Dinfty.CodeB` |
| `D-2814` | theorem | `scottEndP_le_iff` | `Dinfty.CodeB` |
| `D-2815` | theorem | `strictConst_mono` | `Dinfty.CodeB` |
| `D-2816` | theorem | `strictConst_eq_bot_iff` | `Dinfty.CodeB` |
| `D-2817` | theorem | `strictConst_ne_bot` | `Dinfty.CodeB` |
| `D-2818` | theorem | `strictConst_ne_marked` | `Dinfty.CodeB` |
| `D-2819` | theorem | `strictConst_isLUB` | `Dinfty.CodeB` |
| `D-2820` | section | `§ 3.  The seam inequality for tag `B`` | `Dinfty.CodeB` |
| `D-2821` | theorem | `leGlueGen_tagA_tagB_of_le` | `Dinfty.CodeB` |
| `D-2822` | section | `§ 4.  Canon-fixedness of the payloads` | `Dinfty.CodeB` |
| `D-2823` | theorem | `fixed_of_ne_bot` | `Dinfty.CodeB` |
| `D-2824` | theorem | `isLUB_pair_of_le` | `Dinfty.CodeB` |
| `D-2825` | section | `§ 5.  Supremum preservation, away from `⊥`` | `Dinfty.CodeB` |
| `D-2826` | theorem | `sig_isLUB_of_ne_bot` | `Dinfty.CodeB` |
| `D-2827` | section | `§ 6.  The `⊥` payload lands in copy `A`, below the copy it came from` | `Dinfty.CodeB` |
| `D-2828` | theorem | `tagPt_bot_le` | `Dinfty.CodeB` |
| `D-2829` | section | `§ 7.  Monotonicity` | `Dinfty.CodeB` |
| `D-2830` | theorem | `sig_mono` | `Dinfty.CodeB` |
| `D-2831` | section | `§ 8.  Supremum preservation, in full` | `Dinfty.CodeB` |
| `D-2832` | theorem | `sig_isLUB` | `Dinfty.CodeB` |
| `D-2833` | section | `§ 9.  The chain, and the address map` | `Dinfty.CodeB` |
| `D-2834` | def | `chainB` | `Dinfty.CodeB` |
| `D-2835` | theorem | `chainB_le_succ` | `Dinfty.CodeB` |
| `D-2836` | theorem | `chainB_mono` | `Dinfty.CodeB` |
| `D-2837` | def | `codeB` | `Dinfty.CodeB` |
| `D-2838` | theorem | `codeB_isLUB` | `Dinfty.CodeB` |
| `D-2839` | section | `§ 10.  Equivariance` | `Dinfty.CodeB` |
| `D-2840` | theorem | `chainB_cons` | `Dinfty.CodeB` |
| `D-2841` | theorem | `codeB_cons` | `Dinfty.CodeB` |
| `D-2842` | theorem | `codeB_cons_zero` | `Dinfty.CodeB` |
| `D-2843` | theorem | `codeB_cons_one` | `Dinfty.CodeB` |
| `D-2844` | theorem | `codeB_cons_two` | `Dinfty.CodeB` |
| `D-2845` | section | `§ 11.  The three images are disjoint, so the address is recoverable` | `Dinfty.CodeB` |
| `D-2846` | theorem | `strictConst_ne_top` | `Dinfty.CodeB` |
| `D-2847` | theorem | `tagVal_zero` | `Dinfty.CodeB` |
| `D-2848` | theorem | `tagVal_one_bot` | `Dinfty.CodeB` |
| `D-2849` | theorem | `tagVal_one_ne` | `Dinfty.CodeB` |
| `D-2850` | theorem | `tagVal_two_bot` | `Dinfty.CodeB` |
| `D-2851` | theorem | `tagVal_two_ne` | `Dinfty.CodeB` |
| `D-2852` | theorem | `tagVal_zero_ne_one` | `Dinfty.CodeB` |
| `D-2853` | theorem | `tagVal_zero_ne_two` | `Dinfty.CodeB` |
| `D-2854` | theorem | `tagVal_one_ne_two` | `Dinfty.CodeB` |
| `D-2855` | theorem | `sig_ne_of_ne` | `Dinfty.CodeB` |
| `D-2856` | theorem | `sig_injective` | `Dinfty.CodeB` |
| `D-2857` | section | `§ 12.  `codeB` is injective` | `Dinfty.CodeB` |
| `D-2858` | theorem | `codeB_head` | `Dinfty.CodeB` |
| `D-2859` | theorem | `codeB_agree` | `Dinfty.CodeB` |
| `D-2860` | theorem | `codeB_injective` | `Dinfty.CodeB` |
| `D-2861` | section | `§ 13.  …so `ρ` exists` | `Dinfty.CodeB` |
| `D-2862` | def | `Attractor` | `Dinfty.CodeB` |
| `D-2863` | theorem | `codeB_mem_attractor` | `Dinfty.CodeB` |
| `D-2864` | def | `rho` | `Dinfty.CodeB` |
| `D-2865` | theorem | `rho_codeB` | `Dinfty.CodeB` |
| `D-2866` | theorem | `rho_surjective` | `Dinfty.CodeB` |
| `D-2867` | theorem | `rho_sigmaA` | `Dinfty.CodeB` |
| `D-2868` | section | `§ 14.  The attractor is closed under the three maps` | `Dinfty.CodeB` |
| `D-2869` | theorem | `mapsTo_sig` | `Dinfty.CodeB` |
| `D-2870` | theorem | `mapsTo_sigmaA` | `Dinfty.CodeB` |
| `D-2871` | theorem | `mapsTo_sigmaB` | `Dinfty.CodeB` |
| `D-2872` | theorem | `mapsTo_sigmaC` | `Dinfty.CodeB` |
| `D-2873` | def | `attractorEquiv` | `Dinfty.CodeB` |
| `D-2874` | theorem | `codeB_constA` | `Dinfty.CodeB` |
| `D-2875` | theorem | `bot_mem_attractor` | `Dinfty.CodeB` |
| `D-2876` | section | `§ 15.  Each `σ_j` is an order embedding` | `Dinfty.CodeB` |
| `D-2877` | theorem | `strictConst_reflects` | `Dinfty.CodeB` |
| `D-2878` | theorem | `sig_reflects` | `Dinfty.CodeB` |
| `D-2879` | theorem | `sig_le_iff` | `Dinfty.CodeB` |
| `D-2880` | theorem | `codeB_tail_le` | `Dinfty.CodeB` |
| `D-2881` | section | `§ What "continuous" can mean for `ρ`` | `Dinfty.RhoContinuity` |
| `D-2882` | section | `§ 1.  `⊥` is in the attractor, and `ρ` sends it to the `A`-vertex` | `Dinfty.RhoContinuity` |
| `D-2883` | theorem | `codeGamma_constA` | `Dinfty.RhoContinuity` |
| `D-2884` | theorem | `rho_bot_eq` | `Dinfty.RhoContinuity` |
| `D-2885` | section | `§ 2.  No topology with upward-closed opens can work` | `Dinfty.RhoContinuity` |
| `D-2886` | def | `UpwardClosedOpens` | `Dinfty.RhoContinuity` |
| `D-2887` | theorem | `no_continuous_rho_of_upwardClosed` | `Dinfty.RhoContinuity` |
| `D-2888` | section | `§ 3.  The notion this development actually supplies` | `Dinfty.RhoContinuity` |
| `D-2889` | def | `ChainContinuous` | `Dinfty.RhoContinuity` |
| `D-2890` | def | `AddressesConverge` | `Dinfty.RhoContinuity` |
| `D-2891` | section | `§ 4.  The reduction` | `Dinfty.RhoContinuity` |
| `D-2892` | theorem | `dist_rho_le_of_prefix` | `Dinfty.RhoContinuity` |
| `D-2893` | theorem | `chainContinuous_of_addressesConverge` | `Dinfty.RhoContinuity` |
| `D-2894` | section | `§ `AddressesConverge`, proved` | `Dinfty.AddressConvergence` |
| `D-2895` | section | `§ 1.  The three blocked head moves` | `Dinfty.AddressConvergence` |
| `D-2896` | theorem | `not_sig_one_le_zero` | `Dinfty.AddressConvergence` |
| `D-2897` | theorem | `not_sig_two_le_zero` | `Dinfty.AddressConvergence` |
| `D-2898` | theorem | `not_sig_two_le_one` | `Dinfty.AddressConvergence` |
| `D-2899` | section | `§ 2.  The head can only move up` | `Dinfty.AddressConvergence` |
| `D-2900` | theorem | `not_codeB_le_one_zero` | `Dinfty.AddressConvergence` |
| `D-2901` | theorem | `not_codeB_le_two_zero` | `Dinfty.AddressConvergence` |
| `D-2902` | theorem | `not_codeB_le_two_one` | `Dinfty.AddressConvergence` |
| `D-2903` | theorem | `head_le_of_codeB_le` | `Dinfty.AddressConvergence` |
| `D-2904` | section | `§ 3.  So the head is eventually constant` | `Dinfty.AddressConvergence` |
| `D-2905` | theorem | `head_eventually_const` | `Dinfty.AddressConvergence` |
| `D-2906` | section | `§ 4.  The induction` | `Dinfty.AddressConvergence` |
| `D-2907` | theorem | `prefix_stabilizes` | `Dinfty.AddressConvergence` |
| `D-2908` | section | `§ 5.  …which is exactly `AddressesConverge`` | `Dinfty.AddressConvergence` |
| `D-2909` | theorem | `addressesConverge` | `Dinfty.AddressConvergence` |
| `D-2910` | theorem | `rho_chainContinuous` | `Dinfty.AddressConvergence` |
| `D-2911` | section | `§ 6.  Uniqueness of `ρ`, transported to `𝒦`` | `Dinfty.AddressConvergence` |
| `D-2912` | theorem | `rho_unique` | `Dinfty.AddressConvergence` |
| `D-2913` | section | `§ `Φ_tri_v2` in Lean — the tripointed category, and `Φ` as an endofunctor on it` | `Dinfty.PhiTri` |
| `D-2914` | section | `§ The bottom and top of the glued object, over an arbitrary base` | `Dinfty.PhiTri` |
| `D-2915` | theorem | `leGlueGen_tagA_bot` | `Dinfty.PhiTri` |
| `D-2916` | theorem | `leGlueGen_tagC_top` | `Dinfty.PhiTri` |
| `D-2917` | section | `§ The tripointed category` | `Dinfty.PhiTri` |
| `D-2918` | structure | `TriPointed` | `Dinfty.PhiTri` |
| `D-2919` | structure | `TriHom` | `Dinfty.PhiTri` |
| `D-2920` | instance | `inst-TriPointed` | `Dinfty.PhiTri` |
| `D-2921` | def | `TriHom.id` | `Dinfty.PhiTri` |
| `D-2922` | def | `TriHom.comp` | `Dinfty.PhiTri` |
| `D-2923` | section | `§ `Φ_tri_v2` on objects` | `Dinfty.PhiTri` |
| `D-2924` | section | `§ The three distinguished points of the glued object` | `Dinfty.PhiTri` |
| `D-2925` | def | `phiBot` | `Dinfty.PhiTri` |
| `D-2926` | def | `phiTop` | `Dinfty.PhiTri` |
| `D-2927` | def | `phiMid` | `Dinfty.PhiTri` |
| `D-2928` | theorem | `phiMid_val` | `Dinfty.PhiTri` |
| `D-2929` | theorem | `phiMid_ne_phiBot` | `Dinfty.PhiTri` |
| `D-2930` | theorem | `phiMid_ne_phiTop` | `Dinfty.PhiTri` |
| `D-2931` | theorem | `phiBot_ne_phiTop` | `Dinfty.PhiTri` |
| `D-2932` | def | `glueBoundedOrderGen` | `Dinfty.PhiTri` |
| `D-2933` | def | `Phi` | `Dinfty.PhiTri` |
| `D-2934` | section | `§ `Φ_tri_v2` on morphisms, and the functor laws` | `Dinfty.PhiTri` |
| `D-2935` | def | `mapFun` | `Dinfty.PhiTri` |
| `D-2936` | def | `PreservesId` | `Dinfty.PhiTri` |
| `D-2937` | def | `PreservesComp` | `Dinfty.PhiTri` |
| `D-2938` | section | `§ The raw tagwise laws — true, but NOT ingredient 2` | `Dinfty.PhiTri` |
| `D-2939` | theorem | `preservesId` | `Dinfty.PhiTri` |
| `D-2940` | theorem | `preservesComp` | `Dinfty.PhiTri` |
| `D-2941` | section | `§ Ingredient 2 proper: the action on the glued object` | `Dinfty.PhiTri` |
| `D-2942` | structure | `TriEmb` | `Dinfty.PhiTri` |
| `D-2943` | def | `TriEmb.hom` | `Dinfty.PhiTri` |
| `D-2944` | theorem | `glueTwist_self` | `Dinfty.PhiTri` |
| `D-2945` | def | `Phi.map` | `Dinfty.PhiTri` |
| `D-2946` | section | `§ The functor laws on the glued object — ingredient 2` | `Dinfty.PhiTri` |
| `D-2947` | theorem | `Phi.map_id` | `Dinfty.PhiTri` |
| `D-2948` | theorem | `Phi.map_comp` | `Dinfty.PhiTri` |
| `D-2949` | section | `§ The copy-hierarchy: the glued order's edge structure, named` | `Dinfty.CopyHierarchy` |
| `D-2950` | def | `copyIdx` | `Dinfty.CopyHierarchy` |
| `D-2951` | theorem | `copyIdx_inl` | `Dinfty.CopyHierarchy` |
| `D-2952` | theorem | `copyIdx_inr_inl` | `Dinfty.CopyHierarchy` |
| `D-2953` | theorem | `copyIdx_inr_inr` | `Dinfty.CopyHierarchy` |
| `D-2954` | theorem | `copyIdx_mono` | `Dinfty.CopyHierarchy` |
| `D-2955` | theorem | `tagC_sink` | `Dinfty.CopyHierarchy` |
| `D-2956` | theorem | `tagA_source` | `Dinfty.CopyHierarchy` |
| `D-2957` | section | `§ Copy `B`, part 2: the atoms of the seed, and the exclusion` | `Dinfty.CopyBAtoms` |
| `D-2958` | theorem | `hmk'` | `Dinfty.CopyBAtoms` |
| `D-2959` | theorem | `hmtk'` | `Dinfty.CopyBAtoms` |
| `D-2960` | theorem | `hbtk'` | `Dinfty.CopyBAtoms` |
| `D-2961` | section | `§ Everything below a copy-`B` point is copy `A` or copy `B`` | `Dinfty.CopyBAtoms` |
| `D-2962` | theorem | `seed_cases` | `Dinfty.CopyBAtoms` |
| `D-2963` | theorem | `copyA_le_copyB` | `Dinfty.CopyBAtoms` |
| `D-2964` | theorem | `dMid_ne_copyB` | `Dinfty.CopyBAtoms` |
| `D-2965` | section | `§ The atoms of the dualised seed` | `Dinfty.CopyBAtoms` |
| `D-2966` | theorem | `copyA_atom_eq` | `Dinfty.CopyBAtoms` |
| `D-2967` | theorem | `atom_unique_of_dMid_atom` | `Dinfty.CopyBAtoms` |
| `D-2968` | theorem | `atom_copyB_of_two` | `Dinfty.CopyBAtoms` |
| `D-2969` | theorem | `factorPart_le_dMid` | `Dinfty.CopyBAtoms` |
| `D-2970` | theorem | `not_genByFactors_of_two_atoms` | `Dinfty.CopyBAtoms` |
| `D-2971` | section | `§ The seed has at least four elements` | `Dinfty.CopyBAtoms` |
| `D-2972` | def | `gMid` | `Dinfty.CopyBAtoms` |
| `D-2973` | theorem | `gMid_joinIrred` | `Dinfty.CopyBAtoms` |
| `D-2974` | theorem | `gMid_le` | `Dinfty.CopyBAtoms` |
| `D-2975` | theorem | `gMid_ne_marked` | `Dinfty.CopyBAtoms` |
| `D-2976` | theorem | `gMid_ne_gLow` | `Dinfty.CopyBAtoms` |
| `D-2977` | def | `gMidSeed` | `Dinfty.CopyBAtoms` |
| `D-2978` | theorem | `four_le_card_seed` | `Dinfty.CopyBAtoms` |
| `D-2979` | section | `§ The base level has three elements` | `Dinfty.CopyBAtoms` |
| `D-2980` | theorem | `card_D_zero` | `Dinfty.CopyBAtoms` |
| `D-2981` | section | `§ The copy-`B` exclusion` | `Dinfty.CopyBAtoms` |
| `D-2982` | theorem | `copyB_forces_false` | `Dinfty.CopyBAtoms` |
| `D-2983` | section | `§ The copy-`B` half of `CopyBCExcludedFor`` | `Dinfty.CopyBAtoms` |
| `D-2984` | theorem | `copyB_excluded_gen` | `Dinfty.CopyBAtoms` |
| `D-2985` | theorem | `copyBCExcluded_of_C` | `Dinfty.CopyBAtoms` |
| `D-2986` | def | `CopyCExcludedFor` | `Dinfty.CopyBAtoms` |
| `D-2987` | theorem | `copyBC_midInf_of_C` | `Dinfty.CopyBAtoms` |
| `D-2988` | theorem | `copyBC_topJ_of_C` | `Dinfty.CopyBAtoms` |
| `D-2989` | theorem | `twoPointFixed_of_C` | `Dinfty.CopyBAtoms` |
| `D-2990` | section | `§ The cut obstruction` | `Dinfty.CutObstruction` |
| `D-2991` | def | `IsCut` | `Dinfty.CutObstruction` |
| `D-2992` | theorem | `IsCut.isLowerSet` | `Dinfty.CutObstruction` |
| `D-2993` | theorem | `isCut_image` | `Dinfty.CutObstruction` |
| `D-2994` | theorem | `cut_prod` | `Dinfty.CutObstruction` |
| `D-2995` | theorem | `cut_of_orderIso` | `Dinfty.CutObstruction` |
| `D-2996` | section | `§ The obstruction` | `Dinfty.CutObstruction` |
| `D-2997` | theorem | `two_le_card_of_bot_ne_top` | `Dinfty.CutObstruction` |
| `D-2998` | theorem | `no_iso_of_cut` | `Dinfty.CutObstruction` |
| `D-2999` | section | `§ The same, with the bounds supplied as data` | `Dinfty.CutObstruction` |
| `D-3000` | theorem | `cut_prod_bounds` | `Dinfty.CutObstruction` |
| `D-3001` | theorem | `cut_of_orderIso_bounds` | `Dinfty.CutObstruction` |
| `D-3002` | theorem | `no_iso_of_cut_bounds` | `Dinfty.CutObstruction` |
| `D-3003` | section | `§ A natural-valued height, and its additivity on products` | `Dinfty.Height` |
| `D-3004` | def | `below` | `Dinfty.Height` |
| `D-3005` | theorem | `mem_below` | `Dinfty.Height` |
| `D-3006` | theorem | `below_card_lt` | `Dinfty.Height` |
| `D-3007` | def | `ht` | `Dinfty.Height` |
| `D-3008` | theorem | `ht_eq` | `Dinfty.Height` |
| `D-3009` | theorem | `ht_lt_of_lt` | `Dinfty.Height` |
| `D-3010` | theorem | `ht_mono` | `Dinfty.Height` |
| `D-3011` | theorem | `ht_le_of_strictMono` | `Dinfty.Height` |
| `D-3012` | theorem | `ht_orderIso` | `Dinfty.Height` |
| `D-3013` | section | `§ The sup is attained` | `Dinfty.Height` |
| `D-3014` | theorem | `exists_lt_ht_succ` | `Dinfty.Height` |
| `D-3015` | section | `§ Additivity on direct products` | `Dinfty.Height` |
| `D-3016` | theorem | `prod_lt_left` | `Dinfty.Height` |
| `D-3017` | theorem | `prod_lt_right` | `Dinfty.Height` |
| `D-3018` | theorem | `ht_prod` | `Dinfty.Height` |
| `D-3019` | def | `htP` | `Dinfty.Height` |
| `D-3020` | theorem | `le_htP` | `Dinfty.Height` |
| `D-3021` | theorem | `exists_ht_eq_htP` | `Dinfty.Height` |
| `D-3022` | theorem | `htP_orderIso` | `Dinfty.Height` |
| `D-3023` | theorem | `htP_prod` | `Dinfty.Height` |
| `D-3024` | section | `§ The definable finite truncation` | `Dinfty.Truncation` |
| `D-3025` | section | `§ The truncation and its invariance` | `Dinfty.Truncation` |
| `D-3026` | def | `smallPart` | `Dinfty.Truncation` |
| `D-3027` | theorem | `mem_smallPart_map` | `Dinfty.Truncation` |
| `D-3028` | def | `smallPartIso` | `Dinfty.Truncation` |
| `D-3029` | section | `§ The collapse: a tail entirely above the threshold is deleted` | `Dinfty.Truncation` |
| `D-3030` | theorem | `mem_smallPart_prod_right` | `Dinfty.Truncation` |
| `D-3031` | def | `smallPartRightIso` | `Dinfty.Truncation` |
| `D-3032` | section | `§ The necessary condition` | `Dinfty.Truncation` |
| `D-3033` | theorem | `seed_iso_smallPart` | `Dinfty.Truncation` |
| `D-3034` | section | `§ Identifying the surviving side` | `Dinfty.Truncation` |
| `D-3035` | def | `weakBelow` | `Dinfty.Truncation` |
| `D-3036` | instance | `weakBelowOrderBot` | `Dinfty.Truncation` |
| `D-3037` | theorem | `mem_smallPart_prod_left` | `Dinfty.Truncation` |
| `D-3038` | def | `smallPartLeftIso` | `Dinfty.Truncation` |
| `D-3039` | section | `§ The surviving side is an explicit finite product` | `Dinfty.Truncation` |
| `D-3040` | def | `consF` | `Dinfty.Truncation` |
| `D-3041` | theorem | `consF_mem` | `Dinfty.Truncation` |
| `D-3042` | theorem | `consF_not_mem` | `Dinfty.Truncation` |
| `D-3043` | def | `piToWeak` | `Dinfty.Truncation` |
| `D-3044` | theorem | `piToWeak_apply` | `Dinfty.Truncation` |
| `D-3045` | def | `weakBelowPi` | `Dinfty.Truncation` |
| `D-3046` | theorem | `card_weakBelow` | `Dinfty.Truncation` |
| `D-3047` | section | `§ The finite equation` | `Dinfty.Truncation` |
| `D-3048` | theorem | `seed_iso_prod` | `Dinfty.Truncation` |
| `D-3049` | theorem | `card_eq_prod` | `Dinfty.Truncation` |
| `D-3050` | section | `§ The seed comparison, replumbed` | `Dinfty.SeedComparison` |
| `D-3051` | section | `§ Atoms of a product` | `Dinfty.SeedComparison` |
| `D-3052` | def | `atomsProdEquiv` | `Dinfty.SeedComparison` |
| `D-3053` | theorem | `card_atoms_prod` | `Dinfty.SeedComparison` |
| `D-3054` | section | `§ Transporting atoms` | `Dinfty.SeedComparison` |
| `D-3055` | def | `atomsIso` | `Dinfty.SeedComparison` |
| `D-3056` | section | `§ The three necessary equations` | `Dinfty.SeedComparison` |
| `D-3057` | theorem | `card_atoms_eq` | `Dinfty.SeedComparison` |
| `D-3058` | theorem | `htP_eq` | `Dinfty.SeedComparison` |
| `D-3059` | section | `§ The refutations` | `Dinfty.SeedComparison` |
| `D-3060` | theorem | `no_iso_of_card_ne` | `Dinfty.SeedComparison` |
| `D-3061` | theorem | `no_iso_of_atoms_ne` | `Dinfty.SeedComparison` |
| `D-3062` | theorem | `no_iso_of_htP_ne` | `Dinfty.SeedComparison` |
| `D-3063` | section | `§ `k > n` is the first slice at a higher base` | `Dinfty.SliceReduction` |
| `D-3064` | def | `upSetBotIso` | `Dinfty.SliceReduction` |
| `D-3065` | theorem | `stepMap_bot'` | `Dinfty.SliceReduction` |
| `D-3066` | theorem | `iotaD_eq_glueA_ji` | `Dinfty.SliceReduction` |
| `D-3067` | def | `iotaSeedIso` | `Dinfty.SliceReduction` |
| `D-3068` | section | `§ The seed is parametrised, not enumerated` | `Dinfty.SeedParametrisation` |
| `D-3069` | theorem | `stepMap_le_iff_apply` | `Dinfty.SeedParametrisation` |
| `D-3070` | theorem | `stepMap_le_markedPt` | `Dinfty.SeedParametrisation` |
| `D-3071` | section | `§ The finish line` | `Dinfty.FinishLine` |
| `D-3072` | def | `FirstSlice` | `Dinfty.FinishLine` |
| `D-3073` | def | `FirstSliceB` | `Dinfty.FinishLine` |
| `D-3074` | def | `FirstSliceC` | `Dinfty.FinishLine` |
| `D-3075` | theorem | `firstSlice_of` | `Dinfty.FinishLine` |
| `D-3076` | section | `§ Copy `C`, the half where the copy-`B` part is absent` | `Dinfty.CopyCLow` |
| `D-3077` | theorem | `hmk'` | `Dinfty.CopyCLow` |
| `D-3078` | theorem | `hmtk'` | `Dinfty.CopyCLow` |
| `D-3079` | theorem | `hbtk'` | `Dinfty.CopyCLow` |
| `D-3080` | theorem | `joinIrred_endP_top` | `Dinfty.CopyCLow` |
| `D-3081` | section | `§ The seed of a copy-`C` point with `m ≰ x`` | `Dinfty.CopyCLow` |
| `D-3082` | theorem | `seedC_cases` | `Dinfty.CopyCLow` |
| `D-3083` | theorem | `copyA_le_copyC` | `Dinfty.CopyCLow` |
| `D-3084` | theorem | `glueA_ne_copyC` | `Dinfty.CopyCLow` |
| `D-3085` | def | `topSeedC` | `Dinfty.CopyCLow` |
| `D-3086` | def | `midSeedC` | `Dinfty.CopyCLow` |
| `D-3087` | theorem | `midSeedC_lt_topSeedC` | `Dinfty.CopyCLow` |
| `D-3088` | section | `§ The atoms` | `Dinfty.CopyCLow` |
| `D-3089` | theorem | `le_topSeedC` | `Dinfty.CopyCLow` |
| `D-3090` | theorem | `copyA_atom_eqC` | `Dinfty.CopyCLow` |
| `D-3091` | theorem | `atom_uniqueC` | `Dinfty.CopyCLow` |
| `D-3092` | theorem | `atom_copyC_of_two` | `Dinfty.CopyCLow` |
| `D-3093` | theorem | `factorPart_le_topC` | `Dinfty.CopyCLow` |
| `D-3094` | theorem | `not_genByFactors_of_two_atomsC` | `Dinfty.CopyCLow` |
| `D-3095` | section | `§ Four elements, again` | `Dinfty.CopyCLow` |
| `D-3096` | theorem | `four_le_card_seedC` | `Dinfty.CopyCLow` |
| `D-3097` | section | `§ The copy-`C` exclusion, on the `m ≰ x` half` | `Dinfty.CopyCLow` |
| `D-3098` | theorem | `copyC_low_forces_false` | `Dinfty.CopyCLow` |
| `D-3099` | theorem | `copyC_excluded_low` | `Dinfty.CopyCLow` |
| `D-3100` | def | `CopyCHighExcludedFor` | `Dinfty.CopyCLow` |
| `D-3101` | theorem | `copyC_of_high` | `Dinfty.CopyCLow` |
| `D-3102` | theorem | `twoPointFixed_of_CHigh` | `Dinfty.CopyCLow` |
| `D-3103` | section | `§ The base-independent replacement for `4 ≤ card S`` | `Dinfty.SeedCardBound` |
| `D-3104` | theorem | `hmk'` | `Dinfty.SeedCardBound` |
| `D-3105` | theorem | `hmtk'` | `Dinfty.SeedCardBound` |
| `D-3106` | theorem | `hbtk'` | `Dinfty.SeedCardBound` |
| `D-3107` | def | `thr` | `Dinfty.SeedCardBound` |
| `D-3108` | theorem | `thr_joinIrred` | `Dinfty.SeedCardBound` |
| `D-3109` | theorem | `thr_le` | `Dinfty.SeedCardBound` |
| `D-3110` | theorem | `thr_injective` | `Dinfty.SeedCardBound` |
| `D-3111` | def | `seedCopy` | `Dinfty.SeedCardBound` |
| `D-3112` | theorem | `seedCopy_injective` | `Dinfty.SeedCardBound` |
| `D-3113` | theorem | `card_D_lt_card_seed` | `Dinfty.SeedCardBound` |
| `D-3114` | section | `§ The two instances` | `Dinfty.SeedCardBound` |
| `D-3115` | theorem | `card_D_lt_card_seed_B` | `Dinfty.SeedCardBound` |
| `D-3116` | theorem | `card_D_lt_card_seed_C` | `Dinfty.SeedCardBound` |
| `D-3117` | theorem | `card_D_lt_card_seed_notA` | `Dinfty.SeedCardBound` |
| `D-3118` | theorem | `four_le_card_seed_zero` | `Dinfty.SeedCardBound` |
| `D-3119` | section | `§ Paying the bookkeeping debt: shifting the base` | `Dinfty.BaseShift` |
| `D-3120` | def | `push` | `Dinfty.BaseShift` |
| `D-3121` | theorem | `joinIrred_push` | `Dinfty.BaseShift` |
| `D-3122` | def | `shiftStep` | `Dinfty.BaseShift` |
| `D-3123` | def | `shiftMany` | `Dinfty.BaseShift` |
| `D-3124` | section | `§ The other half: only the bottom factor survives` | `Dinfty.BaseShift` |
| `D-3125` | def | `weakBelowSingletonIso` | `Dinfty.BaseShift` |
| `D-3126` | section | `§ The assembly: `FirstSlice` closes every comparison` | `Dinfty.BaseShift` |
| `D-3127` | theorem | `no_comparison_of_firstSlice` | `Dinfty.BaseShift` |
| `D-3128` | section | `§ `StageFixed`, reduced from an arbitrary base stage` | `Dinfty.StageAssembly` |
| `D-3129` | theorem | `hmk` | `Dinfty.StageAssembly` |
| `D-3130` | theorem | `hmtk` | `Dinfty.StageAssembly` |
| `D-3131` | theorem | `hbtk` | `Dinfty.StageAssembly` |
| `D-3132` | section | `§ The copy-`A` exclusion from an arbitrary base stage` | `Dinfty.StageAssembly` |
| `D-3133` | theorem | `copyA_forces_bot_at` | `Dinfty.StageAssembly` |
| `D-3134` | section | `§ The induction step from an arbitrary base stage` | `Dinfty.StageAssembly` |
| `D-3135` | theorem | `copyA_step_at` | `Dinfty.StageAssembly` |
| `D-3136` | section | `§ The two hypothesis families` | `Dinfty.StageAssembly` |
| `D-3137` | def | `CopyBCExcludedAt` | `Dinfty.StageAssembly` |
| `D-3138` | def | `BaseSeparation` | `Dinfty.StageAssembly` |
| `D-3139` | section | `§ The descent, from an arbitrary base stage` | `Dinfty.StageAssembly` |
| `D-3140` | theorem | `stage_of_seed_iso` | `Dinfty.StageAssembly` |
| `D-3141` | section | `§ `StageFixed`` | `Dinfty.StageAssembly` |
| `D-3142` | theorem | `stageFixed_of` | `Dinfty.StageAssembly` |
| `D-3143` | theorem | `colimit_compat_of` | `Dinfty.StageAssembly` |
| `D-3144` | section | `§ The `k = 0` slice is the old statement` | `Dinfty.StageAssembly` |
| `D-3145` | theorem | `copyBCExcludedAt_zero_iff` | `Dinfty.StageAssembly` |
| `D-3146` | section | `§ Copy `B` and copy-`C`-low, from an arbitrary base stage` | `Dinfty.CopyBCAtBase` |
| `D-3147` | section | `§ The single-atom contradiction, at an arbitrary base` | `Dinfty.CopyBCAtBase` |
| `D-3148` | theorem | `single_atom_absurd` | `Dinfty.CopyBCAtBase` |
| `D-3149` | section | `§ Copy `B`` | `Dinfty.CopyBCAtBase` |
| `D-3150` | theorem | `copyB_forces_false_at` | `Dinfty.CopyBCAtBase` |
| `D-3151` | section | `§ Copy `C`, below the marked point` | `Dinfty.CopyBCAtBase` |
| `D-3152` | theorem | `copyC_low_forces_false_at` | `Dinfty.CopyBCAtBase` |
| `D-3153` | section | `§ The single-atom half is unconditional` | `Dinfty.CopyBCAtBase` |
| `D-3154` | def | `CopyBCMultiAtomExcludedAt` | `Dinfty.CopyBCAtBase` |
| `D-3155` | theorem | `copyBCExcludedAt_of_multiAtom` | `Dinfty.CopyBCAtBase` |
| `D-3156` | theorem | `colimit_compat_of_multiAtom` | `Dinfty.CopyBCAtBase` |
| `D-3157` | section | `§ What `GenByFactors` buys, stated where it is true` | `Dinfty.CopyBCAtBase` |
| `D-3158` | def | `CopyCHighExcludedAt` | `Dinfty.CopyBCAtBase` |
| `D-3159` | theorem | `copyBCMultiAtom_of_gen` | `Dinfty.CopyBCAtBase` |
| `D-3160` | section | `§ The remaining obligation, split into its three cases` | `Dinfty.CopyBCAtBase` |
| `D-3161` | def | `MultiAtomB` | `Dinfty.CopyBCAtBase` |
| `D-3162` | def | `MultiAtomCLow` | `Dinfty.CopyBCAtBase` |
| `D-3163` | theorem | `copyBCMultiAtom_of_parts` | `Dinfty.CopyBCAtBase` |
| `D-3164` | theorem | `multiAtomB_of_gen` | `Dinfty.CopyBCAtBase` |
| `D-3165` | theorem | `multiAtomCLow_of_gen` | `Dinfty.CopyBCAtBase` |
| `D-3166` | section | `§ Which pieces fail `GenByFactors`, as a theorem` | `Dinfty.CopyBCAtBase` |
| `D-3167` | theorem | `notGen_base_of_two_atoms_B` | `Dinfty.CopyBCAtBase` |
| `D-3168` | theorem | `notGen_base_of_two_atoms_CLow` | `Dinfty.CopyBCAtBase` |
| `D-3169` | section | `§ Closing the wiring: `FirstSlice` implies `colimit_compat`` | `Dinfty.FirstSliceToColimit` |
| `D-3170` | theorem | `multiAtomExcluded_of_firstSlice` | `Dinfty.FirstSliceToColimit` |
| `D-3171` | theorem | `colimit_compat_of_firstSlice` | `Dinfty.FirstSliceToColimit` |
| `D-3172` | theorem | `colimit_compat_of_firstSlice_parts` | `Dinfty.FirstSliceToColimit` |
| `D-3173` | section | `§ `FirstSliceB` for every level, by the cut obstruction` | `Dinfty.FirstSliceCut` |
| `D-3174` | theorem | `hmk'` | `Dinfty.FirstSliceCut` |
| `D-3175` | theorem | `hmtk'` | `Dinfty.FirstSliceCut` |
| `D-3176` | theorem | `hbtk'` | `Dinfty.FirstSliceCut` |
| `D-3177` | section | `§ Two small `Equiv` combinators` | `Dinfty.FirstSliceCut` |
| `D-3178` | def | `subInter` | `Dinfty.FirstSliceCut` |
| `D-3179` | def | `sndSub` | `Dinfty.FirstSliceCut` |
| `D-3180` | section | `§ `lamD` is join-irreducible` | `Dinfty.FirstSliceCut` |
| `D-3181` | theorem | `joinIrred_lamD` | `Dinfty.FirstSliceCut` |
| `D-3182` | section | `§ The copy-`A` part below the marked point is a product` | `Dinfty.FirstSliceCut` |
| `D-3183` | abbrev | `JMid` | `Dinfty.FirstSliceCut` |
| `D-3184` | theorem | `jMid_nonempty` | `Dinfty.FirstSliceCut` |
| `D-3185` | theorem | `jiOrderIso_le_markedPt` | `Dinfty.FirstSliceCut` |
| `D-3186` | def | `markedSeedEquiv` | `Dinfty.FirstSliceCut` |
| `D-3187` | theorem | `card_markedSeed` | `Dinfty.FirstSliceCut` |
| `D-3188` | section | `§ The cut` | `Dinfty.FirstSliceCut` |
| `D-3189` | def | `cutB` | `Dinfty.FirstSliceCut` |
| `D-3190` | theorem | `cutB_isCut` | `Dinfty.FirstSliceCut` |
| `D-3191` | theorem | `cutB_nonempty` | `Dinfty.FirstSliceCut` |
| `D-3192` | def | `cutBComplEquiv` | `Dinfty.FirstSliceCut` |
| `D-3193` | theorem | `card_cutBCompl` | `Dinfty.FirstSliceCut` |
| `D-3194` | section | `§ The theorem` | `Dinfty.FirstSliceCut` |
| `D-3195` | theorem | `firstSliceB` | `Dinfty.FirstSliceCut` |
| `D-3196` | section | `§ Copy `C` below the marked point` | `Dinfty.FirstSliceCut` |
| `D-3197` | abbrev | `JAll` | `Dinfty.FirstSliceCut` |
| `D-3198` | theorem | `jAll_nonempty` | `Dinfty.FirstSliceCut` |
| `D-3199` | def | `topSeedEquiv` | `Dinfty.FirstSliceCut` |
| `D-3200` | theorem | `card_topSeed` | `Dinfty.FirstSliceCut` |
| `D-3201` | def | `cutC` | `Dinfty.FirstSliceCut` |
| `D-3202` | theorem | `cutC_isCut` | `Dinfty.FirstSliceCut` |
| `D-3203` | theorem | `cutC_nonempty` | `Dinfty.FirstSliceCut` |
| `D-3204` | def | `cutCComplEquiv` | `Dinfty.FirstSliceCut` |
| `D-3205` | theorem | `card_cutCCompl` | `Dinfty.FirstSliceCut` |
| `D-3206` | theorem | `firstSliceC_low` | `Dinfty.FirstSliceCut` |
| `D-3207` | section | `§ What is left: copy `C` above the marked point` | `Dinfty.FirstSliceCut` |
| `D-3208` | def | `FirstSliceCHigh` | `Dinfty.FirstSliceCut` |
| `D-3209` | theorem | `firstSliceC` | `Dinfty.FirstSliceCut` |
| `D-3210` | theorem | `firstSlice` | `Dinfty.FirstSliceCut` |
| `D-3211` | theorem | `colimit_compat_of_firstSliceCHigh` | `Dinfty.FirstSliceCut` |
| `D-3212` | section | `§ Copy `C` above the marked point` | `Dinfty.CopyCHigh` |
| `D-3213` | theorem | `hmk'` | `Dinfty.CopyCHigh` |
| `D-3214` | section | `§ 1. The characterisation` | `Dinfty.CopyCHigh` |
| `D-3215` | theorem | `eq_constHom_of_marked_le` | `Dinfty.CopyCHigh` |
| `D-3216` | theorem | `copyCHigh_shape` | `Dinfty.CopyCHigh` |
| `D-3217` | section | `§ 2. The reduction to divisibility` | `Dinfty.CopyCHigh` |
| `D-3218` | theorem | `firstSliceCHigh_of_card` | `Dinfty.CopyCHigh` |
| `D-3219` | section | `§ 3. The three tag-parts, and their sizes` | `Dinfty.CopyCHigh` |
| `D-3220` | def | `subInter` | `Dinfty.CopyCHigh` |
| `D-3221` | def | `sndSub` | `Dinfty.CopyCHigh` |
| `D-3222` | theorem | `jiOrderIso_le_constHom` | `Dinfty.CopyCHigh` |
| `D-3223` | def | `constSeedEquiv` | `Dinfty.CopyCHigh` |
| `D-3224` | theorem | `card_constSeed` | `Dinfty.CopyCHigh` |
| `D-3225` | section | `§ 4. The tag partition of a copy-`C`-high seed` | `Dinfty.CopyCHigh` |
| `D-3226` | theorem | `hmtk'` | `Dinfty.CopyCHigh` |
| `D-3227` | theorem | `hbtk'` | `Dinfty.CopyCHigh` |
| `D-3228` | theorem | `glueC_le_glueC` | `Dinfty.CopyCHigh` |
| `D-3229` | abbrev | `PartA` | `Dinfty.CopyCHigh` |
| `D-3230` | abbrev | `PartB` | `Dinfty.CopyCHigh` |
| `D-3231` | abbrev | `PartC` | `Dinfty.CopyCHigh` |
| `D-3232` | def | `fromSum` | `Dinfty.CopyCHigh` |
| `D-3233` | theorem | `fromSum_A` | `Dinfty.CopyCHigh` |
| `D-3234` | theorem | `fromSum_B` | `Dinfty.CopyCHigh` |
| `D-3235` | theorem | `fromSum_C` | `Dinfty.CopyCHigh` |
| `D-3236` | theorem | `fromSum_injective` | `Dinfty.CopyCHigh` |
| `D-3237` | theorem | `fromSum_surjective` | `Dinfty.CopyCHigh` |
| `D-3238` | def | `seedSplit` | `Dinfty.CopyCHigh` |
| `D-3239` | theorem | `card_seed_split` | `Dinfty.CopyCHigh` |
| `D-3240` | section | `§ 5. The three sizes, and the contradiction` | `Dinfty.CopyCHigh` |
| `D-3241` | theorem | `card_partA` | `Dinfty.CopyCHigh` |
| `D-3242` | theorem | `card_partB` | `Dinfty.CopyCHigh` |
| `D-3243` | theorem | `card_partC` | `Dinfty.CopyCHigh` |
| `D-3244` | theorem | `three_le_card_D` | `Dinfty.CopyCHigh` |
| `D-3245` | theorem | `not_card_dvd` | `Dinfty.CopyCHigh` |
| `D-3246` | theorem | `firstSliceCHigh` | `Dinfty.CopyCHigh` |
| `D-3247` | theorem | `firstSlice` | `Dinfty.CopyCHigh` |
| `D-3248` | theorem | `colimit_compat` | `Dinfty.CopyCHigh` |
| `D-3249` | theorem | `DBilimit_rigid` | `Dinfty.CopyCHigh` |
| `D-3250` | section | `§ `B` and `DBilimit` are not the same domain` | `Dinfty.BilimitGap` |
| `D-3251` | section | `§ 1.  ω-compactness, and its invariance` | `Dinfty.BilimitGap` |
| `D-3252` | def | `OmegaCompact` | `Dinfty.BilimitGap` |
| `D-3253` | theorem | `OmegaCompact.map` | `Dinfty.BilimitGap` |
| `D-3254` | section | `§ 2.  In `DBilimit` the top is not compact` | `Dinfty.BilimitGap` |
| `D-3255` | theorem | `topSeq_not_omegaCompact` | `Dinfty.BilimitGap` |
| `D-3256` | section | `§ 3.  In `B` the top IS compact` | `Dinfty.BilimitGap` |
| `D-3257` | theorem | `topB_val` | `Dinfty.BilimitGap` |
| `D-3258` | theorem | `level_top_succ` | `Dinfty.BilimitGap` |
| `D-3259` | theorem | `eq_topB_of_zero_top` | `Dinfty.BilimitGap` |
| `D-3260` | theorem | `le_topB` | `Dinfty.BilimitGap` |
| `D-3261` | theorem | `topB_omegaCompact` | `Dinfty.BilimitGap` |
| `D-3262` | section | `§ 4.  So there is no order isomorphism` | `Dinfty.BilimitGap` |
| `D-3263` | theorem | `no_orderIso` | `Dinfty.BilimitGap` |
| `D-3264` | section | `§ 5.  What an identification would have bought` | `Dinfty.BilimitGap` |
| `D-3265` | theorem | `rigid_of_orderIso` | `Dinfty.BilimitGap` |
| `D-3266` | section | `§ Copy `A` is a proper order-ideal, and that is which object is which` | `Dinfty.CopyIdeal` |
| `D-3267` | def | `CopyA` | `Dinfty.CopyIdeal` |
| `D-3268` | theorem | `copyA_isLowerSet` | `Dinfty.CopyIdeal` |
| `D-3269` | theorem | `not_mem_copyA_of_isTop` | `Dinfty.CopyIdeal` |
| `D-3270` | section | `§ At the tower` | `Dinfty.CopyIdeal` |
| `D-3271` | theorem | `iotaD_mem_copyA` | `Dinfty.CopyIdeal` |
| `D-3272` | theorem | `legacy_confined_phi_not` | `Dinfty.CopyIdeal` |
| `D-3273` | section | `§ Does Theorem B's rigidity survive from the copy-`A` ideal to the whole?` | `Dinfty.StageRigidity` |
| `D-3274` | section | `§ 1.  The stage maps are order-embeddings` | `Dinfty.StageRigidity` |
| `D-3275` | theorem | `ins_le_iff` | `Dinfty.StageRigidity` |
| `D-3276` | theorem | `ins_le_iff'` | `Dinfty.StageRigidity` |
| `D-3277` | theorem | `ins_injective` | `Dinfty.StageRigidity` |
| `D-3278` | section | `§ 2.  The two hypotheses` | `Dinfty.StageRigidity` |
| `D-3279` | def | `StageDefinable` | `Dinfty.StageRigidity` |
| `D-3280` | def | `LevelsMaximallyRigid` | `Dinfty.StageRigidity` |
| `D-3281` | section | `§ 3.  The transport` | `Dinfty.StageRigidity` |
| `D-3282` | theorem | `eq_on_stages` | `Dinfty.StageRigidity` |
| `D-3283` | theorem | `eq_refl_of_fixes_stages` | `Dinfty.StageRigidity` |
| `D-3284` | theorem | `eq_refl_of_stageDefinable` | `Dinfty.StageRigidity` |
| `D-3285` | theorem | `rigid_of_stageDefinable` | `Dinfty.StageRigidity` |
| `D-3286` | section | `§ 4.  At the `Φ`-tower` | `Dinfty.StageRigidity` |
| `D-3287` | def | `PhiStageDefinable` | `Dinfty.StageRigidity` |
| `D-3288` | theorem | `levels_maximally_rigid` | `Dinfty.StageRigidity` |
| `D-3289` | theorem | `B_rigid_of_stageDefinable` | `Dinfty.StageRigidity` |
| `D-3290` | theorem | `eq_id_of_stageDefinable` | `Dinfty.StageRigidity` |
| `D-3291` | section | `§ Why restriction to the copy-`A` ideal cannot be the route` | `Dinfty.StageRigidity` |
| `D-3292` | theorem | `legacy_subtower` | `Dinfty.StageRigidity` |
| `D-3293` | theorem | `phi_emb_top_not_legacy` | `Dinfty.StageRigidity` |
| `D-3294` | theorem | `ins_top` | `Dinfty.StageRigidity` |
| `D-3295` | section | `§ The two pillars now rest on one reduction` | `Dinfty.StageRigidity` |
| `D-3296` | theorem | `pillars_share_one_reduction` | `Dinfty.StageRigidity` |
| `D-3297` | section | `§ Cleaning the residue: `PhiStageDefinable` down to one level-local `Prop`` | `Dinfty.PhiStagePipe` |
| `D-3298` | section | `§ 0.  The stage inclusion, with its domain spelled as a level` | `Dinfty.PhiStagePipe` |
| `D-3299` | def | `insD` | `Dinfty.PhiStagePipe` |
| `D-3300` | theorem | `insD_le_iff` | `Dinfty.PhiStagePipe` |
| `D-3301` | theorem | `insD_monotone` | `Dinfty.PhiStagePipe` |
| `D-3302` | theorem | `insD_le_self` | `Dinfty.PhiStagePipe` |
| `D-3303` | section | `§ 1.  The two routine `Prop`s, discharged` | `Dinfty.PhiStagePipe` |
| `D-3304` | theorem | `stageSupClosed` | `Dinfty.PhiStagePipe` |
| `D-3305` | def | `stageJI` | `Dinfty.PhiStagePipe` |
| `D-3306` | theorem | `stageJoinRecoverable` | `Dinfty.PhiStagePipe` |
| `D-3307` | section | `§ 2.  The stages are exactly the compact elements` | `Dinfty.PhiStagePipe` |
| `D-3308` | theorem | `insD_omegaCompact` | `Dinfty.PhiStagePipe` |
| `D-3309` | theorem | `exists_stage_of_omegaCompact` | `Dinfty.PhiStagePipe` |
| `D-3310` | theorem | `omegaCompact_iff_stage` | `Dinfty.PhiStagePipe` |
| `D-3311` | theorem | `stages_union_preserved` | `Dinfty.PhiStagePipe` |
| `D-3312` | section | `§ 3.  RETIRED: the join-irreducible route` | `Dinfty.PhiStagePipe` |
| `D-3313` | section | `§ 4.  What the residue is already pinned at` | `Dinfty.PhiStagePipe` |
| `D-3314` | theorem | `apply_insD_bot` | `Dinfty.PhiStagePipe` |
| `D-3315` | theorem | `apply_insD_top` | `Dinfty.PhiStagePipe` |
| `D-3316` | section | `§ What an automorphism of `B` looks like on a stage` | `Dinfty.StageEmbedding` |
| `D-3317` | section | `§ 1.  The stage is a bounded sub-join-semilattice` | `Dinfty.StageEmbedding` |
| `D-3318` | theorem | `insD_le_insD_iff` | `Dinfty.StageEmbedding` |
| `D-3319` | theorem | `insD_injective` | `Dinfty.StageEmbedding` |
| `D-3320` | theorem | `insD_bot` | `Dinfty.StageEmbedding` |
| `D-3321` | theorem | `insD_top` | `Dinfty.StageEmbedding` |
| `D-3322` | def | `embD` | `Dinfty.StageEmbedding` |
| `D-3323` | theorem | `insD_embD` | `Dinfty.StageEmbedding` |
| `D-3324` | theorem | `insD_isLUB_pair` | `Dinfty.StageEmbedding` |
| `D-3325` | theorem | `embD_sup` | `Dinfty.StageEmbedding` |
| `D-3326` | section | `§ 2.  The stage map of an automorphism` | `Dinfty.StageEmbedding` |
| `D-3327` | theorem | `stage_map_exists` | `Dinfty.StageEmbedding` |
| `D-3328` | theorem | `stage_map_comp` | `Dinfty.StageEmbedding` |
| `D-3329` | section | `§ 3.  The residue, level-local` | `Dinfty.StageEmbedding` |
| `D-3330` | def | `LevelEmbUnique` | `Dinfty.StageEmbedding` |
| `D-3331` | theorem | `levelEmbUnique_diagonal` | `Dinfty.StageEmbedding` |
| `D-3332` | theorem | `phiStageDefinable_of_levelEmbUnique` | `Dinfty.StageEmbedding` |
| `D-3333` | theorem | `B_rigid_of_levelEmbUnique` | `Dinfty.StageEmbedding` |
| `D-3334` | section | `§ `embD`, formalized: the residue is only about the **image**` | `Dinfty.EmbDImage` |
| `D-3335` | section | `§ 1.  The staged ep-pair, abstractly` | `Dinfty.EmbDImage` |
| `D-3336` | theorem | `prjLe_embLe` | `Dinfty.EmbDImage` |
| `D-3337` | theorem | `embLe_prjLe_le` | `Dinfty.EmbDImage` |
| `D-3338` | section | `§ 2.  `prjD`, and the image of `embD`` | `Dinfty.EmbDImage` |
| `D-3339` | def | `prjD` | `Dinfty.EmbDImage` |
| `D-3340` | theorem | `prjD_embD` | `Dinfty.EmbDImage` |
| `D-3341` | theorem | `embD_prjD_le` | `Dinfty.EmbDImage` |
| `D-3342` | theorem | `prjD_monotone` | `Dinfty.EmbDImage` |
| `D-3343` | theorem | `embD_le_iff` | `Dinfty.EmbDImage` |
| `D-3344` | theorem | `embD_monotone` | `Dinfty.EmbDImage` |
| `D-3345` | theorem | `embD_injective` | `Dinfty.EmbDImage` |
| `D-3346` | theorem | `mem_range_embD_iff` | `Dinfty.EmbDImage` |
| `D-3347` | section | `§ 3.  `embD` satisfies every hypothesis of the residue` | `Dinfty.EmbDImage` |
| `D-3348` | theorem | `embD_bot` | `Dinfty.EmbDImage` |
| `D-3349` | theorem | `embD_top` | `Dinfty.EmbDImage` |
| `D-3350` | section | `§ 4.  Measuring the image` | `Dinfty.EmbDImage` |
| `D-3351` | theorem | `ncard_range_embD` | `Dinfty.EmbDImage` |
| `D-3352` | theorem | `ncard_range_of_reflecting` | `Dinfty.EmbDImage` |
| `D-3353` | theorem | `range_eq_of_subset` | `Dinfty.EmbDImage` |
| `D-3354` | section | `§ 5.  The reduction: only the image matters` | `Dinfty.EmbDImage` |
| `D-3355` | theorem | `eq_embD_of_range_subset` | `Dinfty.EmbDImage` |
| `D-3356` | section | `§ 6.  The residue, restated as an image statement` | `Dinfty.EmbDImage` |
| `D-3357` | def | `LevelImageStable` | `Dinfty.EmbDImage` |
| `D-3358` | theorem | `levelEmbUnique_of_levelImageStable` | `Dinfty.EmbDImage` |
| `D-3359` | theorem | `B_rigid_of_levelImageStable` | `Dinfty.EmbDImage` |
| `D-3360` | section | `§ 7.  And only at join-irreducibles` | `Dinfty.EmbDImage` |
| `D-3361` | theorem | `range_embD_sup_closed` | `Dinfty.EmbDImage` |
| `D-3362` | theorem | `range_embD_bot_mem` | `Dinfty.EmbDImage` |
| `D-3363` | theorem | `finset_sup_mem_range` | `Dinfty.EmbDImage` |
| `D-3364` | theorem | `map_finset_sup` | `Dinfty.EmbDImage` |
| `D-3365` | theorem | `image_stable_of_joinIrred` | `Dinfty.EmbDImage` |
| `D-3366` | def | `LevelImageStableJI` | `Dinfty.EmbDImage` |
| `D-3367` | theorem | `levelImageStable_of_JI` | `Dinfty.EmbDImage` |
| `D-3368` | theorem | `B_rigid_of_levelImageStableJI` | `Dinfty.EmbDImage` |
| `D-3369` | section | `§ 8.  The chain, in one place — and it is refuted` | `Dinfty.EmbDImage` |
| `D-3370` | theorem | `rigidity_finish_line` | `Dinfty.EmbDImage` |
| `D-3371` | theorem | `levelImageStable_diagonal` | `Dinfty.EmbDImage` |
| `D-3372` | section | `§ The tower's embeddings are tagwise, and so is their image` | `Dinfty.EmbTagwise` |
| `D-3373` | section | `§ 1.  `canonGen` is inert on the image of an injective tripointed map` | `Dinfty.EmbTagwise` |
| `D-3374` | theorem | `ne_mark_of_canon_tagC` | `Dinfty.EmbTagwise` |
| `D-3375` | theorem | `canonGen_baseMapGen` | `Dinfty.EmbTagwise` |
| `D-3376` | theorem | `phiFun_val_tagwise` | `Dinfty.EmbTagwise` |
| `D-3377` | theorem | `baseMapGen_copyIdx` | `Dinfty.EmbTagwise` |
| `D-3378` | section | `§ 2.  At the `Φ`-iterate tower` | `Dinfty.EmbTagwise` |
| `D-3379` | theorem | `hmk'` | `Dinfty.EmbTagwise` |
| `D-3380` | theorem | `hbtk'` | `Dinfty.EmbTagwise` |
| `D-3381` | theorem | `endDownFun_endUpFun` | `Dinfty.EmbTagwise` |
| `D-3382` | theorem | `endUpFun_injective` | `Dinfty.EmbTagwise` |
| `D-3383` | theorem | `emb_succ_val` | `Dinfty.EmbTagwise` |
| `D-3384` | theorem | `emb_succ_copyIdx` | `Dinfty.EmbTagwise` |
| `D-3385` | section | `§ 3.  The image, tagwise` | `Dinfty.EmbTagwise` |
| `D-3386` | theorem | `mem_range_emb_succ_iff` | `Dinfty.EmbTagwise` |
| `D-3387` | theorem | `range_val_emb_succ_inl` | `Dinfty.EmbTagwise` |
| `D-3388` | section | `§ The residue only needs *cofinally many* levels` | `Dinfty.StageCofinal` |
| `D-3389` | section | `§ 1.  One stable level is a *fixed* level` | `Dinfty.StageCofinal` |
| `D-3390` | theorem | `fixes_stage` | `Dinfty.StageCofinal` |
| `D-3391` | section | `§ 2.  Cofinally many stable levels suffice` | `Dinfty.StageCofinal` |
| `D-3392` | def | `StageDefinableCofinal` | `Dinfty.StageCofinal` |
| `D-3393` | theorem | `stageDefinable_cofinal` | `Dinfty.StageCofinal` |
| `D-3394` | theorem | `fixes_stages_below` | `Dinfty.StageCofinal` |
| `D-3395` | theorem | `eq_refl_of_cofinal_stable` | `Dinfty.StageCofinal` |
| `D-3396` | theorem | `rigid_of_cofinal_stageDefinable` | `Dinfty.StageCofinal` |
| `D-3397` | section | `§ 3.  Stage maps, named` | `Dinfty.StageCofinal` |
| `D-3398` | def | `IsStageMap` | `Dinfty.StageCofinal` |
| `D-3399` | theorem | `stage_map_exists'` | `Dinfty.StageCofinal` |
| `D-3400` | theorem | `IsStageMap.unique` | `Dinfty.StageCofinal` |
| `D-3401` | theorem | `IsStageMap.monotone` | `Dinfty.StageCofinal` |
| `D-3402` | theorem | `IsStageMap.reflect` | `Dinfty.StageCofinal` |
| `D-3403` | theorem | `IsStageMap.injective` | `Dinfty.StageCofinal` |
| `D-3404` | theorem | `IsStageMap.push` | `Dinfty.StageCofinal` |
| `D-3405` | theorem | `isStageMap_coherent` | `Dinfty.StageCofinal` |
| `D-3406` | section | `§ 4.  The diagonal collapses` | `Dinfty.StageCofinal` |
| `D-3407` | theorem | `IsStageMap.diagonal` | `Dinfty.StageCofinal` |
| `D-3408` | theorem | `IsStageMap.fixes` | `Dinfty.StageCofinal` |
| `D-3409` | section | `§ 5.  At the `Φ`-tower` | `Dinfty.StageCofinal` |
| `D-3410` | def | `PhiStageDefinableCofinal` | `Dinfty.StageCofinal` |
| `D-3411` | theorem | `phiStageDefinable_cofinal` | `Dinfty.StageCofinal` |
| `D-3412` | theorem | `eq_id_of_cofinal` | `Dinfty.StageCofinal` |
| `D-3413` | theorem | `B_rigid_of_cofinal` | `Dinfty.StageCofinal` |
| `D-3414` | section | `§ The singular atom of an arbitrary slice — and why it does not reach `B`` | `Dinfty.AtomlessBilimit` |
| `D-3415` | section | `§ 1.  Spikes` | `Dinfty.AtomlessBilimit` |
| `D-3416` | theorem | `spikeHom_ne_bot` | `Dinfty.AtomlessBilimit` |
| `D-3417` | theorem | `spikeHom_injective` | `Dinfty.AtomlessBilimit` |
| `D-3418` | theorem | `spikeHom_ne_constHom` | `Dinfty.AtomlessBilimit` |
| `D-3419` | theorem | `eq_bot_of_apply_top` | `Dinfty.AtomlessBilimit` |
| `D-3420` | section | `§ 2.  The atom of a slice, in closed form` | `Dinfty.AtomlessBilimit` |
| `D-3421` | theorem | `eq_lamD` | `Dinfty.AtomlessBilimit` |
| `D-3422` | theorem | `bot_val_succ` | `Dinfty.AtomlessBilimit` |
| `D-3423` | theorem | `glueA_ne_bot_of_ne_bot` | `Dinfty.AtomlessBilimit` |
| `D-3424` | theorem | `ne_bot_of_tagA` | `Dinfty.AtomlessBilimit` |
| `D-3425` | theorem | `lamD_succ` | `Dinfty.AtomlessBilimit` |
| `D-3426` | section | `§ 3.  Tripointed ep-pairs transport spikes` | `Dinfty.AtomlessBilimit` |
| `D-3427` | theorem | `prj_eq_top_iff` | `Dinfty.AtomlessBilimit` |
| `D-3428` | theorem | `endUpFun_spikeHom` | `Dinfty.AtomlessBilimit` |
| `D-3429` | theorem | `emb_succ_glueA` | `Dinfty.AtomlessBilimit` |
| `D-3430` | section | `§ 4.  The base fattens the spike` | `Dinfty.AtomlessBilimit` |
| `D-3431` | theorem | `base_emb_lamD_ne` | `Dinfty.AtomlessBilimit` |
| `D-3432` | section | `§ 5.  …and every level inherits it` | `Dinfty.AtomlessBilimit` |
| `D-3433` | theorem | `emb_lamD_ne` | `Dinfty.AtomlessBilimit` |
| `D-3434` | section | `§ 6.  `B` is atomless` | `Dinfty.AtomlessBilimit` |
| `D-3435` | theorem | `botB_eq_bot` | `Dinfty.AtomlessBilimit` |
| `D-3436` | theorem | `exists_ne_bot_component` | `Dinfty.AtomlessBilimit` |
| `D-3437` | theorem | `stage_atom_lt` | `Dinfty.AtomlessBilimit` |
| `D-3438` | theorem | `exists_lt_lt_of_ne_bot` | `Dinfty.AtomlessBilimit` |
| `D-3439` | theorem | `no_isAtom` | `Dinfty.AtomlessBilimit` |
| `D-3440` | section | `§ Copy `A` is a principal ideal` | `Dinfty.SeamFixed` |
| `D-3441` | section | `§ 1.  Every point occurs among its own occurrences` | `Dinfty.SeamFixed` |
| `D-3442` | theorem | `leGlueGen_tagA_top` | `Dinfty.SeamFixed` |
| `D-3443` | section | `§ 2.  The seam point of a level, and copy `A` as a principal ideal` | `Dinfty.SeamFixed` |
| `D-3444` | def | `cSeam` | `Dinfty.SeamFixed` |
| `D-3445` | theorem | `cSeam_val` | `Dinfty.SeamFixed` |
| `D-3446` | theorem | `le_cSeam_of_tagA` | `Dinfty.SeamFixed` |
| `D-3447` | theorem | `tagA_of_le_cSeam` | `Dinfty.SeamFixed` |
| `D-3448` | theorem | `mem_copyA_iff_le_cSeam` | `Dinfty.SeamFixed` |
| `D-3449` | section | `§ 3.  One point pins the copy-`A` split` | `Dinfty.SeamFixed` |
| `D-3450` | theorem | `copyA_preserved` | `Dinfty.SeamFixed` |
| `D-3451` | theorem | `copyA_mapsTo` | `Dinfty.SeamFixed` |
| `D-3452` | section | `§ `LevelEmbUnique` is FALSE — and obstruction (T) is what refutes it` | `Dinfty.PatchedEmbedding` |
| `D-3453` | section | `§ 1.  `⊤` is join-irreducible at every level` | `Dinfty.PatchedEmbedding` |
| `D-3454` | theorem | `top_joinIrred` | `Dinfty.PatchedEmbedding` |
| `D-3455` | section | `§ 2.  The patched inclusion` | `Dinfty.PatchedEmbedding` |
| `D-3456` | def | `patched` | `Dinfty.PatchedEmbedding` |
| `D-3457` | theorem | `patched_of_ne_top` | `Dinfty.PatchedEmbedding` |
| `D-3458` | theorem | `patched_top` | `Dinfty.PatchedEmbedding` |
| `D-3459` | theorem | `patched_bot` | `Dinfty.PatchedEmbedding` |
| `D-3460` | theorem | `patched_monotone` | `Dinfty.PatchedEmbedding` |
| `D-3461` | theorem | `patched_reflect` | `Dinfty.PatchedEmbedding` |
| `D-3462` | theorem | `patched_sup` | `Dinfty.PatchedEmbedding` |
| `D-3463` | section | `§ 3.  It is not the canonical embedding` | `Dinfty.PatchedEmbedding` |
| `D-3464` | theorem | `patched_val_ne_top` | `Dinfty.PatchedEmbedding` |
| `D-3465` | section | `§ 4.  The refutation` | `Dinfty.PatchedEmbedding` |
| `D-3466` | theorem | `hmt1` | `Dinfty.PatchedEmbedding` |
| `D-3467` | theorem | `hbt1` | `Dinfty.PatchedEmbedding` |
| `D-3468` | theorem | `top_val_two` | `Dinfty.PatchedEmbedding` |
| `D-3469` | def | `wB` | `Dinfty.PatchedEmbedding` |
| `D-3470` | theorem | `wB_val` | `Dinfty.PatchedEmbedding` |
| `D-3471` | theorem | `wB_ne_top` | `Dinfty.PatchedEmbedding` |
| `D-3472` | theorem | `copyIdx_wB` | `Dinfty.PatchedEmbedding` |
| `D-3473` | theorem | `not_levelEmbUnique` | `Dinfty.PatchedEmbedding` |
| `D-3474` | theorem | `not_levelImageStable` | `Dinfty.PatchedEmbedding` |
| `D-3475` | theorem | `not_levelImageStableJI` | `Dinfty.PatchedEmbedding` |
| `D-3476` | section | `§ Hunting the automorphism instead of the invariant` | `Dinfty.StageCover` |
| `D-3477` | section | `§ 1.  `endUpFun` transports constants` | `Dinfty.StageCover` |
| `D-3478` | theorem | `endUpFun_constHom` | `Dinfty.StageCover` |
| `D-3479` | theorem | `emb_eq_top_iff` | `Dinfty.StageCover` |
| `D-3480` | section | `§ 2.  `patched` is coherent with the tower` | `Dinfty.StageCover` |
| `D-3481` | theorem | `patched_coherent` | `Dinfty.StageCover` |
| `D-3482` | section | `§ 3.  The tower's embeddings preserve the copy index, level to level` | `Dinfty.StageCover` |
| `D-3483` | theorem | `embD_copyIdx` | `Dinfty.StageCover` |
| `D-3484` | section | `§ 4.  The stage maps of an automorphism cover the filtration` | `Dinfty.StageCover` |
| `D-3485` | theorem | `stage_map_covers` | `Dinfty.StageCover` |
| `D-3486` | section | `§ 5.  The verdict: the §117 freedom is not invertible` | `Dinfty.StageCover` |
| `D-3487` | theorem | `no_patched_automorphism` | `Dinfty.StageCover` |
| `D-3488` | section | `§ Splitting again: the canonical chain, and the first point that discriminates` | `Dinfty.CanonicalChain` |
| `D-3489` | section | `§ 0.  Two spellings the tower needs` | `Dinfty.CanonicalChain` |
| `D-3490` | theorem | `top_val_succ` | `Dinfty.CanonicalChain` |
| `D-3491` | theorem | `cSeam_ne_top` | `Dinfty.CanonicalChain` |
| `D-3492` | theorem | `insD_emb` | `Dinfty.CanonicalChain` |
| `D-3493` | section | `§ 1.  The seam is level-stable above the base` | `Dinfty.CanonicalChain` |
| `D-3494` | theorem | `endUpFun_top` | `Dinfty.CanonicalChain` |
| `D-3495` | theorem | `emb_cSeam_succ` | `Dinfty.CanonicalChain` |
| `D-3496` | theorem | `base_emb_cSeam_ne` | `Dinfty.CanonicalChain` |
| `D-3497` | section | `§ 2.  The canonical point` | `Dinfty.CanonicalChain` |
| `D-3498` | def | `cSeamB` | `Dinfty.CanonicalChain` |
| `D-3499` | theorem | `insD_cSeam` | `Dinfty.CanonicalChain` |
| `D-3500` | section | `§ 3.  The chain` | `Dinfty.CanonicalChain` |
| `D-3501` | theorem | `midB_lt_cSeamB` | `Dinfty.CanonicalChain` |
| `D-3502` | theorem | `cSeamB_lt_top` | `Dinfty.CanonicalChain` |
| `D-3503` | theorem | `le_cSeamB_iff` | `Dinfty.CanonicalChain` |
| `D-3504` | section | `§ 4.  The seam discriminates, where the mid does not` | `Dinfty.CanonicalChain` |
| `D-3505` | theorem | `iotaD_preserves_mid` | `Dinfty.CanonicalChain` |
| `D-3506` | theorem | `patched_ne_cSeam` | `Dinfty.CanonicalChain` |
| `D-3507` | def | `CSeamFixed` | `Dinfty.CanonicalChain` |
| `D-3508` | section | `§ `Fix σ_A` is not a singleton — Theorem ESCAPE fails for the `constHom` IFS` | `Dinfty.EscapeAnalysis` |
| `D-3509` | section | `§ `pLeg` of the marked tag-`A` point` | `Dinfty.EscapeAnalysis` |
| `D-3510` | theorem | `pLeg_markedB` | `Dinfty.EscapeAnalysis` |
| `D-3511` | section | `§ The marked point is fixed` | `Dinfty.EscapeAnalysis` |
| `D-3512` | theorem | `sigmaA_mid` | `Dinfty.EscapeAnalysis` |
| `D-3513` | theorem | `mid_mem_fix` | `Dinfty.EscapeAnalysis` |
| `D-3514` | section | `§ …and it is in the orbit of `⊥`` | `Dinfty.EscapeAnalysis` |
| `D-3515` | theorem | `tagB_bot_eq_mark` | `Dinfty.EscapeAnalysis` |
| `D-3516` | theorem | `sigmaB_bot` | `Dinfty.EscapeAnalysis` |
| `D-3517` | section | `§ Theorem ESCAPE fails` | `Dinfty.EscapeAnalysis` |
| `D-3518` | theorem | `fix_sigmaA_not_singleton` | `Dinfty.EscapeAnalysis` |
| `D-3519` | theorem | `no_fixA` | `Dinfty.EscapeAnalysis` |
| `D-3520` | section | `§ `CSeamFixed`: the seam is a cut point — and the decision is NOT reached` | `Dinfty.SeamCut` |
| `D-3521` | section | `§ 1.  The seam is the bottom of copy `C`` | `Dinfty.SeamCut` |
| `D-3522` | theorem | `canon_tagC_bot` | `Dinfty.SeamCut` |
| `D-3523` | theorem | `cSeam_le_iff` | `Dinfty.SeamCut` |
| `D-3524` | section | `§ 2.  Fixing the seam = preserving the copy-`A` ideal` | `Dinfty.SeamCut` |
| `D-3525` | theorem | `cSeamFixed_iff_ideal_stable` | `Dinfty.SeamCut` |
| `D-3526` | section | `§ 3.  Why the local handles fail` | `Dinfty.SeamCut` |
| `D-3527` | theorem | `spikeHom_lamD_le` | `Dinfty.SeamCut` |
| `D-3528` | section | `§ The global invariants, applied to the seam` | `Dinfty.IdealInvariant` |
| `D-3529` | section | `§ 1.  The invariant` | `Dinfty.IdealInvariant` |
| `D-3530` | def | `idealIso` | `Dinfty.IdealInvariant` |
| `D-3531` | theorem | `theta_cSeamB_stage` | `Dinfty.IdealInvariant` |
| `D-3532` | theorem | `cSeamFixed_of_ideal_pins` | `Dinfty.IdealInvariant` |
| `D-3533` | section | `§ 2.  Inside a level, the invariant decides every comparable case` | `Dinfty.IdealInvariant` |
| `D-3534` | theorem | `ideal_ncard_lt_of_lt` | `Dinfty.IdealInvariant` |
| `D-3535` | theorem | `ideal_ncard_lt_of_gt` | `Dinfty.IdealInvariant` |
| `D-3536` | theorem | `not_idealIso_of_ne_of_comp` | `Dinfty.IdealInvariant` |
| `D-3537` | section | `§ 3.  What is left, named` | `Dinfty.IdealInvariant` |
| `D-3538` | theorem | `comparable_or_tagB` | `Dinfty.IdealInvariant` |
| `D-3539` | section | `§ Running the split: `LevelImageStableJI` cannot be proved generically` | `Dinfty.LevelEmbNotGeneric` |
| `D-3540` | def | `embChainA` | `Dinfty.LevelEmbNotGeneric` |
| `D-3541` | def | `embChainB` | `Dinfty.LevelEmbNotGeneric` |
| `D-3542` | theorem | `embChainA_mono` | `Dinfty.LevelEmbNotGeneric` |
| `D-3543` | theorem | `embChainB_mono` | `Dinfty.LevelEmbNotGeneric` |
| `D-3544` | theorem | `embChainA_reflect` | `Dinfty.LevelEmbNotGeneric` |
| `D-3545` | theorem | `embChainB_reflect` | `Dinfty.LevelEmbNotGeneric` |
| `D-3546` | theorem | `embChainA_bot` | `Dinfty.LevelEmbNotGeneric` |
| `D-3547` | theorem | `embChainB_bot` | `Dinfty.LevelEmbNotGeneric` |
| `D-3548` | theorem | `embChainA_top` | `Dinfty.LevelEmbNotGeneric` |
| `D-3549` | theorem | `embChainB_top` | `Dinfty.LevelEmbNotGeneric` |
| `D-3550` | theorem | `embChainA_sup` | `Dinfty.LevelEmbNotGeneric` |
| `D-3551` | theorem | `embChainB_sup` | `Dinfty.LevelEmbNotGeneric` |
| `D-3552` | theorem | `embChain_ne` | `Dinfty.LevelEmbNotGeneric` |
| `D-3553` | theorem | `chain_not_unique` | `Dinfty.LevelEmbNotGeneric` |
| `D-3554` | section | `§ `CoreIFS` is a triangle, not a triple` | `Dinfty.SeamTriangle` |
| `D-3555` | section | `§ 1.  The abstract triangle` | `Dinfty.SeamTriangle` |
| `D-3556` | def | `Seamed` | `Dinfty.SeamTriangle` |
| `D-3557` | def | `Seamless` | `Dinfty.SeamTriangle` |
| `D-3558` | theorem | `not_seamed_of_seamless` | `Dinfty.SeamTriangle` |
| `D-3559` | theorem | `fix_disjoint_of_seamless` | `Dinfty.SeamTriangle` |
| `D-3560` | section | `§ 2.  The third seam, at the tower` | `Dinfty.SeamTriangle` |
| `D-3561` | theorem | `tagC_mark_eq_tagB_top` | `Dinfty.SeamTriangle` |
| `D-3562` | section | `§ 3.  `Γ` is seamed` | `Dinfty.SeamTriangle` |
| `D-3563` | def | `fseq` | `Dinfty.SeamTriangle` |
| `D-3564` | def | `gseq` | `Dinfty.SeamTriangle` |
| `D-3565` | theorem | `fseq_zero` | `Dinfty.SeamTriangle` |
| `D-3566` | theorem | `fseq_one` | `Dinfty.SeamTriangle` |
| `D-3567` | theorem | `fseq_two` | `Dinfty.SeamTriangle` |
| `D-3568` | theorem | `gseq_zero` | `Dinfty.SeamTriangle` |
| `D-3569` | theorem | `gseq_one` | `Dinfty.SeamTriangle` |
| `D-3570` | theorem | `gseq_two` | `Dinfty.SeamTriangle` |
| `D-3571` | theorem | `seam_AB` | `Dinfty.SeamTriangle` |
| `D-3572` | theorem | `seam_AC` | `Dinfty.SeamTriangle` |
| `D-3573` | theorem | `seam_BC` | `Dinfty.SeamTriangle` |
| `D-3574` | theorem | `gasket_seamed` | `Dinfty.SeamTriangle` |
| `D-3575` | section | `§ 4.  The address space is seamless` | `Dinfty.SeamTriangle` |
| `D-3576` | theorem | `cons_const` | `Dinfty.SeamTriangle` |
| `D-3577` | theorem | `cons_eq_self` | `Dinfty.SeamTriangle` |
| `D-3578` | theorem | `address_seamless` | `Dinfty.SeamTriangle` |
| `D-3579` | theorem | `fix_cons` | `Dinfty.SeamTriangle` |
| `D-3580` | section | `§ 5.  `ρ` is the map that installs the seams` | `Dinfty.SeamTriangle` |
| `D-3581` | theorem | `codeGamma_cons` | `Dinfty.SeamTriangle` |
| `D-3582` | theorem | `codeGamma_const` | `Dinfty.SeamTriangle` |
| `D-3583` | theorem | `codeGamma_seam` | `Dinfty.SeamTriangle` |
| `D-3584` | theorem | `codeB_seam_ne` | `Dinfty.SeamTriangle` |
| `D-3585` | theorem | `codeB_seamless` | `Dinfty.SeamTriangle` |
| `D-3586` | theorem | `codeB_not_seamed` | `Dinfty.SeamTriangle` |
| `D-3587` | theorem | `rho_not_injective` | `Dinfty.SeamTriangle` |
| `D-3588` | section | `§ 6.  The openness failure is at the `a`/`b` seam` | `Dinfty.SeamTriangle` |
| `D-3589` | theorem | `mid_eq_seam` | `Dinfty.SeamTriangle` |
| `D-3590` | theorem | `openness_fails_at_seam` | `Dinfty.SeamTriangle` |
| `D-3591` | section | `§ 7.  `fix_card`'s `fixB`/`fixC`: unsatisfiable inside `Core`` | `Dinfty.SeamTriangle` |
| `D-3592` | theorem | `fix_sig_inter_attractor` | `Dinfty.SeamTriangle` |
| `D-3593` | theorem | `no_fixData_address` | `Dinfty.SeamTriangle` |
| `D-3594` | def | `inDeg` | `Dinfty.SeamTriangle` |
| `D-3595` | theorem | `inDeg_zero` | `Dinfty.SeamTriangle` |
| `D-3596` | theorem | `inDeg_one` | `Dinfty.SeamTriangle` |
| `D-3597` | theorem | `inDeg_two` | `Dinfty.SeamTriangle` |
| `D-3598` | section | `§ 8.  The shape the redefinition should take` | `Dinfty.SeamTriangle` |
| `D-3599` | structure | `SeamedIFS` | `Dinfty.SeamTriangle` |
| `D-3600` | def | `addressSeamedIFS` | `Dinfty.SeamTriangle` |
| `D-3601` | section | `§ `Dinfty.Verify` — the single entry point for an independent check` | `Dinfty.Verify` |
| `D-3602` | example | `example-phiB` | `Dinfty.Verify` |
| `D-3603` | example | `example-Subsingleton` | `Dinfty.Verify` |
| `D-3604` | example | `example-Subsingleton` | `Dinfty.Verify` |
| `D-3605` | example | `example-InternalIFS` | `Dinfty.Verify` |
| `D-3606` | example | `example-Injective` | `Dinfty.Verify` |
| `D-3607` | example | `example-Injective` | `Dinfty.Verify` |
| `D-3608` | example | `example-Injective` | `Dinfty.Verify` |
| `D-3609` | example | `example-B` | `Dinfty.Verify` |
| `D-3610` | example | `example-sigmaA` | `Dinfty.Verify` |
| `D-3611` | example | `example-sigmaB` | `Dinfty.Verify` |
| `D-3612` | example | `example-InternalIFS` | `Dinfty.Verify` |
| `D-3613` | example | `example-Injective` | `Dinfty.Verify` |
| `D-3614` | example | `example-Injective` | `Dinfty.Verify` |
| `D-3615` | example | `example-Injective` | `Dinfty.Verify` |
| `D-3616` | example | `example-sigmaA` | `Dinfty.Verify` |
| `D-3617` | example | `example-midB` | `Dinfty.Verify` |
| `D-3618` | example | `example-True` | `Dinfty.Verify` |
| `D-3619` | example | `example-D` | `Dinfty.Verify` |
| `D-3620` | example | `example-D` | `Dinfty.Verify` |
| `D-3621` | example | `example-prj` | `Dinfty.Verify` |
| `D-3622` | example | `example-Fix` | `Dinfty.Verify` |
| `D-3623` | section | `§ `Γ` is a definition, not a parameter` | `Dinfty.Verify` |
| `D-3624` | example | `example-gasketSet` | `Dinfty.Verify` |
| `D-3625` | example | `example-Nontrivial` | `Dinfty.Verify` |
| `D-3626` | section | `§ The coding map `π : {A,B,C}^ℕ ↠ Γ`` | `Dinfty.Verify` |
| `D-3627` | example | `example-Continuous` | `Dinfty.Verify` |
| `D-3628` | example | `example-Surjective` | `Dinfty.Verify` |
| `D-3629` | example | `example` | `Dinfty.Verify` |
| `D-3630` | example | `example` | `Dinfty.Verify` |
| `D-3631` | example | `example-IsQuotientMap` | `Dinfty.Verify` |
| `D-3632` | example | `example` | `Dinfty.Verify` |
| `D-3633` | example | `example-Gamma` | `Dinfty.Verify` |
| `D-3634` | section | `§ The address map into `B`, and `ρ`` | `Dinfty.Verify` |
| `D-3635` | example | `example-Fin` | `Dinfty.Verify` |
| `D-3636` | example | `example-Injective` | `Dinfty.Verify` |
| `D-3637` | example | `example-Surjective` | `Dinfty.Verify` |
| `D-3638` | example | `example` | `Dinfty.Verify` |
| `D-3639` | example | `example-Fin` | `Dinfty.Verify` |
| `D-3640` | example | `example-Disjoint` | `Dinfty.Verify` |
| `D-3641` | example | `example-B` | `Dinfty.Verify` |
| `D-3642` | section | `§ Which topology `ρ` can be continuous for` | `Dinfty.Verify` |
| `D-3643` | example | `example-rho` | `Dinfty.Verify` |
| `D-3644` | example | `example-TopologicalSpace` | `Dinfty.Verify` |
| `D-3645` | example | `example-AddressesConverge` | `Dinfty.Verify` |
| `D-3646` | example | `example-ChainContinuous` | `Dinfty.Verify` |
| `D-3647` | example | `example-Attractor` | `Dinfty.Verify` |
| `D-3648` | example | `example-Fin` | `Dinfty.Verify` |
| `D-3649` | section | `§ Theorem A and Theorem B are about DIFFERENT domains` | `Dinfty.Verify` |
| `D-3650` | example | `example` | `Dinfty.Verify` |
| `D-3651` | example | `example-OmegaCompact` | `Dinfty.Verify` |
| `D-3652` | example | `example` | `Dinfty.Verify` |
| `D-3653` | example | `example` | `Dinfty.Verify` |
| `D-3654` | example | `example-B` | `Dinfty.Verify` |
| `D-3655` | section | `§ Axiom dependencies` | `Dinfty.Verify` |
| `D-3656` | section | `§ The seam triangle` | `Dinfty.Verify` |
| `D-3657` | example | `example-tagB_bot_eq_mark` | `Dinfty.Verify` |
| `D-3658` | example | `example-tagC_bot_eq_top` | `Dinfty.Verify` |
| `D-3659` | example | `example-tagC_mark_eq_tagB_top` | `Dinfty.Verify` |
| `D-3660` | example | `example-Seamed` | `Dinfty.Verify` |
| `D-3661` | example | `example-Seamless` | `Dinfty.Verify` |
| `D-3662` | example | `example-Seamless` | `Dinfty.Verify` |
| `D-3663` | example | `example-Fin` | `Dinfty.Verify` |
| `D-3664` | example | `example-Fin` | `Dinfty.Verify` |
| `D-3665` | example | `example-Fin` | `Dinfty.Verify` |
| `D-3666` | example | `example` | `Dinfty.Verify` |
| `D-3667` | example | `example-mid` | `Dinfty.Verify` |
| `D-3668` | example | `example-Fin` | `Dinfty.Verify` |
| `D-3669` | example | `example-Fin` | `Dinfty.Verify` |
| `D-3670` | example | `example-FixPoints` | `Dinfty.Verify` |
| `D-3671` | section | `§ From the copy-`A` ideal to the whole` | `Dinfty.Verify` |
| `D-3672` | example | `example-B` | `Dinfty.Verify` |
| `D-3673` | example | `example-LevelsMaximallyRigid` | `Dinfty.Verify` |
| `D-3674` | example | `example-PhiStageDefinable` | `Dinfty.Verify` |
| `D-3675` | example | `example-D` | `Dinfty.Verify` |
| `D-3676` | example | `example-D` | `Dinfty.Verify` |
| `D-3677` | section | `§ The residue, cleaned` | `Dinfty.Verify` |
| `D-3678` | example | `example-D` | `Dinfty.Verify` |
| `D-3679` | example | `example-Set` | `Dinfty.Verify` |
| `D-3680` | example | `example-D` | `Dinfty.Verify` |
| `D-3681` | example | `example-B` | `Dinfty.Verify` |
| `D-3682` | example | `example-B` | `Dinfty.Verify` |
| `D-3683` | example | `example-B` | `Dinfty.Verify` |
| `D-3684` | example | `example-B` | `Dinfty.Verify` |
| `D-3685` | section | `§ The residue is level-local` | `Dinfty.Verify` |
| `D-3686` | example | `example-B` | `Dinfty.Verify` |
| `D-3687` | example | `example-k` | `Dinfty.Verify` |
| `D-3688` | example | `example-D` | `Dinfty.Verify` |
| `D-3689` | example | `example-LevelEmbUnique` | `Dinfty.Verify` |
| `D-3690` | section | `§ `embD`, and the residue as an image statement` | `Dinfty.Verify` |
| `D-3691` | example | `example-k` | `Dinfty.Verify` |
| `D-3692` | example | `example-k` | `Dinfty.Verify` |
| `D-3693` | example | `example-k` | `Dinfty.Verify` |
| `D-3694` | example | `example-k` | `Dinfty.Verify` |
| `D-3695` | example | `example-k` | `Dinfty.Verify` |
| `D-3696` | example | `example-k` | `Dinfty.Verify` |
| `D-3697` | example | `example-k` | `Dinfty.Verify` |
| `D-3698` | example | `example-k` | `Dinfty.Verify` |
| `D-3699` | example | `example-LevelImageStableJI` | `Dinfty.Verify` |
| `D-3700` | section | `§ The embeddings are tagwise, and copy `A` is a principal ideal` | `Dinfty.Verify` |
| `D-3701` | example | `example-D` | `Dinfty.Verify` |
| `D-3702` | example | `example-D` | `Dinfty.Verify` |
| `D-3703` | example | `example-D` | `Dinfty.Verify` |
| `D-3704` | example | `example-D` | `Dinfty.Verify` |
| `D-3705` | example | `example-D` | `Dinfty.Verify` |
| `D-3706` | example | `example-D` | `Dinfty.Verify` |
| `D-3707` | section | `§ Running the split: no generic proof of the residue exists` | `Dinfty.Verify` |
| `D-3708` | example | `example` | `Dinfty.Verify` |
| `D-3709` | section | `§ The residue chain is REFUTED` | `Dinfty.Verify` |
| `D-3710` | example | `example-Monotone` | `Dinfty.Verify` |
| `D-3711` | example | `example-D` | `Dinfty.Verify` |
| `D-3712` | example | `example-D` | `Dinfty.Verify` |
| `D-3713` | example | `example-D` | `Dinfty.Verify` |
| `D-3714` | example | `example` | `Dinfty.Verify` |
| `D-3715` | example | `example` | `Dinfty.Verify` |
| `D-3716` | section | `§ The residue, weakened: cofinally many stable levels` | `Dinfty.Verify` |
| `D-3717` | example | `example-B` | `Dinfty.Verify` |
| `D-3718` | example | `example-B` | `Dinfty.Verify` |
| `D-3719` | example | `example-B` | `Dinfty.Verify` |
| `D-3720` | example | `example-PhiStageDefinableCofinal` | `Dinfty.Verify` |
| `D-3721` | example | `example-PhiStageDefinable` | `Dinfty.Verify` |
| `D-3722` | section | `§ The singular atom of a slice does not reach `B`` | `Dinfty.Verify` |
| `D-3723` | example | `example-lamD` | `Dinfty.Verify` |
| `D-3724` | example | `example-TriEP` | `Dinfty.Verify` |
| `D-3725` | example | `example` | `Dinfty.Verify` |
| `D-3726` | example | `example` | `Dinfty.Verify` |
| `D-3727` | example | `example-B` | `Dinfty.Verify` |
| `D-3728` | section | `§ The hunt: is the §117 freedom invertible?` | `Dinfty.Verify` |
| `D-3729` | example | `example-TriEP` | `Dinfty.Verify` |
| `D-3730` | example | `example-D` | `Dinfty.Verify` |
| `D-3731` | example | `example-D` | `Dinfty.Verify` |
| `D-3732` | example | `example-B` | `Dinfty.Verify` |
| `D-3733` | section | `§ Splitting again: the canonical chain` | `Dinfty.Verify` |
| `D-3734` | example | `example` | `Dinfty.Verify` |
| `D-3735` | example | `example` | `Dinfty.Verify` |
| `D-3736` | example | `example-insD` | `Dinfty.Verify` |
| `D-3737` | example | `example-midB` | `Dinfty.Verify` |
| `D-3738` | example | `example-cSeamB` | `Dinfty.Verify` |
| `D-3739` | example | `example-D` | `Dinfty.Verify` |
| `D-3740` | example | `example-iotaD` | `Dinfty.Verify` |
| `D-3741` | example | `example-patched` | `Dinfty.Verify` |
| `D-3742` | section | `§ `CSeamFixed`: structure settled, decision NOT reached` | `Dinfty.Verify` |
| `D-3743` | example | `example-D` | `Dinfty.Verify` |
| `D-3744` | example | `example-CSeamFixed` | `Dinfty.Verify` |
| `D-3745` | example | `example-EndP` | `Dinfty.Verify` |
| `D-3746` | section | `§ The global invariants at the seam` | `Dinfty.Verify` |
| `D-3747` | example | `example-B` | `Dinfty.Verify` |
| `D-3748` | example | `example-B` | `Dinfty.Verify` |
| `D-3749` | example | `example` | `Dinfty.Verify` |
| `D-3750` | example | `example-D` | `Dinfty.Verify` |
| `D-3751` | example | `example-D` | `Dinfty.Verify` |
| `D-3752` | theorem | `no_orderIso_DInfty` | `Dinfty.BilimitGap` |
| `D-3753` | example | `example` | `Dinfty.Verify` |
