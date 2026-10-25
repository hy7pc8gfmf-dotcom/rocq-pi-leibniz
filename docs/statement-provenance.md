# Statement provenance (companion document)

Statement-level migration provenance for the rocq-pi-leibniz
package: for each statement, the source statement of the
development it was migrated from, with the source coordinates
recorded at migration time (coordinates frozen as recorded).
Maintained outside the library per package comment policy;
citations inside the library are by fully qualified name.

Blocks below are migrated verbatim from the library files at
package state 52d41fa (v1.0.3-prep).

## PiKernelSlack.v statement-provenance ledger (719 entries)

Migrated from [theories/Reals/Cauchy/PiKernelSlack.v] lines 17403-18131.

```coq

(* -----------------------------------------------------------------------
   Statement provenance: each entry lists a statement of this file and,
   where the statement restates a result of the source development, the
   source file and line recorded at migration time (coordinates frozen
   as recorded).  Entries marked "new in this file" are statements
   introduced here.
   ----------------------------------------------------------------------- *)
(*
   1. [And] -- new in this file
   2. [NatLe] -- new in this file
   3. [NatLe_drop] -- source: S01_BaseRing.v@91
   4. [NatLe_lift] -- new in this file
   5. [QltT_to_Qlt] -- source: S02_CauchyComplete.v@50
   6. [Qlt_to_QltT] -- new in this file
   7. [QleT'_to_Qle] -- source: S02_CauchyComplete.v@103
   8. [Qle_to_QleT'] -- source: S02_CauchyComplete.v@115
   9. [qleT'_refl] -- source: S02_CauchyComplete.v@182
  10. [qleT'_trans] -- source: S02_CauchyComplete.v@201
  11. [qeq_le] -- new in this file
  12. [Qle_plus_nonneg_r] -- source: S02_CauchyComplete.v@529
  13. [qleT'_plus_nonneg_rT] -- source: S02_CauchyComplete.v@227
  14. [qeq_leT'] -- new in this file
  15. [qleT'_plus_compat] -- new in this file
  16. [q_neq_of_lt] -- source: S03_QExp.v@84
  17. [Qle_div_same_denom] -- source: S03_QExp.v@110
  18. [q_le_div_le] -- new in this file
  19. [q_lt_0_odd_den] -- new in this file
  20. [sc_lpa_decr_le] -- source: S10_KVQuantTrig.v@2710
  21. [sc_lpa_nonneg] -- source: S10_KVQuantTrig.v@2719
  22. [sc_lp_pair_nonneg] -- source: S10_KVQuantTrig.v@2727
  23. [sc_lp_odd_mono] -- source: S10_KVQuantTrig.v@2734
  24. [sc_lp_odd_chain] -- new in this file
  25. [nat_le_Sn_n_absurd] -- new in this file
  26. [sc_lp_ev_decr] -- new in this file
  27. [sc_lp_ev_le_s6] -- new in this file
  28. [sc_lp_odd_le_s6] -- source: S10_KVQuantTrig.v@8775
  29. [sc_lp_four_nonneg] -- new in this file
  30. [sc_lp_three_value] -- new in this file
  31. [sc_lp_three_margin] -- new in this file
  32. [sc_lp_six_value] -- new in this file
  33. [sc_lp_six_margin] -- new in this file
  34. [piL_xL_under_ten_thirds] -- new in this file
  35. [piL_xL_over_three] -- new in this file
  36. [piL_ten_thirds_supply] -- new in this file
  37. [piL_leibniz_ten_thirds_supply] -- new in this file
  38. [piL_three_supply] -- new in this file
  39. [piL_hn0g2_under_ten_thirds] -- new in this file
  40. [QPoly] -- source: LW0PiIrrational.v@48
  41. [qpoly_add] -- source: LW0PiIrrational.v@51
  42. [qpoly_scalar] -- source: LW0PiIrrational.v@59
  43. [qpoly_mul] -- new in this file
  44. [qpoly_eval] -- source: LW0PiIrrational.v@77
  45. [qpoly_deriv] -- source: LW0PiIrrational.v@101
  46. [qpoly_deriv_iter] -- new in this file
  47. [q_pow] -- source: S03_QExp.v@36
  48. [q_fact] -- new in this file
  49. [q_lt_0_succ_den] -- source: S03_QExp.v@70
  50. [q_fact_pos] -- new in this file
  51. [lw0_alt] -- source: LW0PiIrrational.v@4292
  52. [lw0_q_pow_pos] -- new in this file
  53. [lw0_QltT_le] -- new in this file
  54. [lw0_Wb] -- source: LW0PiIrrational.v@1336
  55. [lw0_Wb_pos] -- new in this file
  56. [lw0_sin_aux] -- source: LW0PiIrrational.v@3473
  57. [lw0_sin_qp] -- new in this file
  58. [lw0_F_aux] -- source: LW0PiIrrational.v@4337
  59. [lw0_F] -- new in this file
  60. [lw0_pi_mono] -- new in this file
  61. [lw0_pi_qminus_pow] -- new in this file
  62. [lw0_niven_f] -- new in this file
  63. [lw0_n_select] -- new in this file
  64. [lw0_pi_d0_of] -- new in this file
  65. [leibsep_qlt_wd2] -- source: LW0LeibSeparation.v@67
  66. [leibsep_qle_wd2] -- source: LW0LeibSeparation.v@74
  67. [leibsep_qlt_minus] -- source: LW0LeibSeparation.v@81
  68. [leibsep_qlt_of_minus] -- source: LW0LeibSeparation.v@84
  69. [leibsep_qle_minus] -- source: LW0LeibSeparation.v@87
  70. [leibsep_qle_of_minus] -- source: LW0LeibSeparation.v@90
  71. [leibsep_qlt_1] -- source: LW0LeibSeparation.v@93
  72. [leibsep_qlt_half] -- source: LW0LeibSeparation.v@96
  73. [leibsep_qlt_half_1] -- new in this file
  74. [leibsep_qabs_le_two] -- new in this file
  75. [lw0_opp_le_swap] -- new in this file
  76. [leibsep_abs_ge_self] -- source: LW0LeibSeparation.v@1896
  77. [leibsep_abs_ge_opp] -- new in this file
  78. [leibsep_qeq_le] -- new in this file
  79. [leibsep_abssum] -- source: LW0LeibSeparation.v@914
  80. [leibsep_abssum_cos] -- new in this file
  81. [leibsep_shore_upper] -- new in this file
  82. [leibsep_shore_W_le] -- new in this file
  83. [leibsep_shore_gap_upper] -- new in this file
  84. [q_pow_succ] -- source: S03_QExp.v@64
  85. [q_fact_succ] -- source: S03_QExp.v@67
  86. [q_pow_abs] -- source: S03_QExp.v@54
  87. [q_pow_nonneg] -- source: S03_QExp.v@77
  88. [q_pow_mono] -- source: S03_QExp.v@774
  89. [q_pow_wd] -- new in this file
  90. [q_succ_add] -- new in this file
  91. [q_pow_diff_bound] -- new in this file
  92. [q_ratio_cancel_succ] -- new in this file
  93. [sin_term] -- new in this file
  94. [cos_term] -- source: S10_KVQuantTrig.v@1213
  95. [sin_partial] -- source: S10_KVQuantTrig.v@1217
  96. [cos_partial] -- source: S10_KVQuantTrig.v@1224
  97. [sc_q_pow_one] -- source: S10_KVQuantTrig.v@1231
  98. [sc_abs_sign] -- new in this file
  99. [sc_sin_term_diff] -- new in this file
 100. [sc_cos_term_diff] -- new in this file
 101. [leibsep_sin_partial_lipschitz] -- source: LW0LeibSeparation.v@929
 102. [leibsep_cos_partial_lipschitz] -- new in this file
 103. [qeq_imp_qle] -- source: S02_CauchyComplete.v@130
 104. [qeq_ltT] -- source: S02_CauchyComplete.v@297
 105. [lw0_q_eq_le] -- source: LW0PiIrrational.v@4034
 106. [lw0_q_of_nat] -- source: LW0PiIrrational.v@397
 107. [lw0_q_of_nat_nonneg] -- source: LW0PiIrrational.v@400
 108. [lw0_q_of_nat_ge_one] -- source: LW0PiIrrational.v@407
 109. [lw0_q_of_nat_le_succ] -- source: LW0PiIrrational.v@414
 110. [lw0_q_of_nat_le_add] -- source: LW0PiIrrational.v@421
 111. [lw0_q_of_nat_le_mono] -- source: LW0PiIrrational.v@1141
 112. [lw0_q_of_nat_succ] -- source: LW0PiIrrational.v@1145
 113. [lw0_q_of_nat_add] -- source: LW0PiIrrational.v@1149
 114. [lw0_q_mult_le_l] -- new in this file
 115. [lw0_pitS_qne0_of_pos] -- source: LW0PiIrrational.v@8949
 116. [lw0_pitS_qof_add] -- source: LW0PiIrrational.v@8962
 117. [lw0_pitS_qof_mul] -- source: LW0PiIrrational.v@8969
 118. [lw0_pitS_qmult_reg_r] -- new in this file
 119. [lw0_pi_d0_absorb] -- source: LW0PiIrrational.v@9530
 120. [lw0_pi_b_den_pos] -- new in this file
 121. [qpoly_eval_add] -- new in this file
 122. [qpoly_eval_scalar] -- new in this file
 123. [qpoly_eval_deriv_cons] -- new in this file
 124. [lw0_q_int_inv] -- new in this file
 125. [lw0_q_div_int_mul] -- new in this file
 126. [lw0_qp_ai] -- new in this file
 127. [lw0_qp_antideriv] -- new in this file
 128. [lw0_qp_ai_cons_eval] -- new in this file
 129. [lw0_qp_ai_zero_head_eval] -- new in this file
 130. [lw0_qp_ai_add] -- new in this file
 131. [lw0_qp_ai_scalar] -- new in this file
 132. [lw0_qp_ai_deriv_pair] -- new in this file
 133. [lw0_qp_antideriv_deriv] -- new in this file
 134. [lw0_qp_ai_deriv_ft] -- new in this file
 135. [lw0_qp_antideriv_deriv_at] -- new in this file
 136. [lw0_qp_deriv_iter_plus] -- new in this file
 137. [lw0_qp_pair] -- new in this file
 138. [lw0_qp_ai_mul_add_l] -- new in this file
 139. [lw0_qp_pair_add_l] -- new in this file
 140. [lw0_q_pow_zero_succ] -- new in this file
 141. [lw0_qp_ai_deriv_ft_pow] -- new in this file
 142. [lw0_qp_pair_ibp_family] -- new in this file
 143. [lw0_qp_pair_ibp] -- new in this file
 144. [lw0_cos_aux] -- new in this file
 145. [lw0_cos_qp] -- new in this file
 146. [lw0_sin_aux_eval] -- new in this file
 147. [lw0_sin_partial_zero] -- new in this file
 148. [lw0_sin_qp_eval] -- new in this file
 149. [lw0_sin_qp_zero_eval] -- new in this file
 150. [lw0_cos_aux_eval] -- new in this file
 151. [lw0_cos_partial_zero] -- new in this file
 152. [lw0_cos_qp_eval] -- new in this file
 153. [lw0_cos_qp_zero_eval] -- new in this file
 154. [lw0_q_div_int_mul_gen] -- new in this file
 155. [lw0_sin_aux_deriv_eval] -- new in this file
 156. [lw0_cos_aux_deriv_eval_S] -- new in this file
 157. [lw0_sin_qp_deriv_eval] -- new in this file
 158. [lw0_cos_qp_deriv_eval] -- new in this file
 159. [qpoly_map] -- new in this file
 160. [lw0_q_abs_div] -- new in this file
 161. [lw0_qp_ai_abs_bound] -- new in this file
 162. [lw0_die] -- new in this file
 163. [lw0_alt_opp] -- new in this file
 164. [lw0_Qmake_succ_eq] -- new in this file
 165. [lw0_coef] -- new in this file
 166. [lw0_coef_add] -- new in this file
 167. [lw0_coef_scalar] -- new in this file
 168. [lw0_coef_deriv] -- new in this file
 169. [lw0_coef_iter_mul] -- new in this file
 170. [lw0_coef_iter_add] -- new in this file
 171. [lw0_coef_iter_scalar] -- new in this file
 172. [lw0_die_budget_mono] -- new in this file
 173. [lw0_die_scalar] -- new in this file
 174. [lw0_die_add] -- new in this file
 175. [lw0_die_mul_sharp] -- new in this file
 176. [lw0_pi_mono_die] -- new in this file
 177. [lw0_pi_qminus_pow_die] -- new in this file
 178. [lw0_niven_f_die] -- new in this file
 179. [lw0_qpoly_eq] -- new in this file
 180. [qpoly_shift] -- new in this file
 181. [lw0_qmake_Z_succ] -- new in this file
 182. [lw0_qmake_add] -- new in this file
 183. [lw0_qmake_2] -- new in this file
 184. [lw0_qmake_1] -- new in this file
 185. [lw0_qpoly_eq_refl] -- new in this file
 186. [lw0_qpoly_eq_sym] -- new in this file
 187. [lw0_qpoly_eq_trans] -- new in this file
 188. [lw0_cons_congr] -- new in this file
 189. [lw0_qpoly_eq_add] -- new in this file
 190. [lw0_qpoly_add_assoc] -- new in this file
 191. [lw0_qpoly_eq_deriv] -- new in this file
 192. [lw0_coef_shift] -- new in this file
 193. [lw0_coef_shift_1] -- new in this file
 194. [lw0_coef_shift_2] -- new in this file
 195. [lw0_coef_shift_lt] -- new in this file
 196. [lw0_shift1_deriv_coef] -- new in this file
 197. [lw0_shift_add] -- new in this file
 198. [lw0_shift_shift] -- new in this file
 199. [lw0_shift_congr] -- new in this file
 200. [lw0_cons2_shift2] -- new in this file
 201. [lw0_scal_pair_shift] -- new in this file
 202. [lw0_sin_aux_scal_append] -- new in this file
 203. [lw0_cos_aux_congr] -- new in this file
 204. [lw0_sin_aux_congr] -- new in this file
 205. [lw0_Wp] -- new in this file
 206. [lw0_Xc] -- new in this file
 207. [lw0_Wp_nil] -- new in this file
 208. [lw0_Xc_nil] -- new in this file
 209. [lw0_Wp_push] -- new in this file
 210. [lw0_Xc_push] -- new in this file
 211. [lw0_sin_qmake_key] -- new in this file
 212. [lw0_cos_qmake_key] -- new in this file
 213. [lw0_sin_aux_deriv_poly_gen] -- new in this file
 214. [lw0_cos_aux_deriv_S_poly_gen] -- new in this file
 215. [lw0_sin_qp_deriv_poly] -- new in this file
 216. [lw0_cos_qp_deriv_poly] -- new in this file
 217. [lw0_sin_qp_deriv2] -- new in this file
 218. [lw0_pitB_conv_zero_shift] -- new in this file
 219. [QeqT] -- source: S02_CauchyComplete.v@303
 220. [qeq_imp_qeqT] -- source: S02_CauchyComplete.v@309
 221. [qeqT_imp_qeq] -- new in this file
 222. [lw0_qpoly_eqT] -- new in this file
 223. [lw385_q_fact_neq] -- new in this file
 224. [lw385_Qplus_eq_compat_r] -- new in this file
 225. [lw385_Qplus_eq_compat2] -- new in this file
 226. [lw385_eq_Id] -- new in this file
 227. [lw385_andb_Id] -- new in this file
 228. [lw385_die_length] -- new in this file
 229. [lw385_coef_len_zero] -- new in this file
 230. [lw385_die_coef_zero] -- new in this file
 231. [lw385_F_aux_plus_deriv2_coef] -- new in this file
 232. [lw385_F_plus_deriv2_coef] -- new in this file
 233. [lw385_F_plus_deriv2_coef_niven] -- new in this file
 234. [lw385_ai_mul_zero] -- new in this file
 235. [lw385_ai_mul_congr_eval] -- new in this file
 236. [lw385_pair_congr_l] -- new in this file
 237. [lw385_pair_F_plus_deriv2] -- new in this file
 238. [lw385_pair_F_plus_deriv2_niven] -- new in this file
 239. [lw385_flip_aux] -- new in this file
 240. [lw385_q_pow_neg_even] -- new in this file
 241. [lw385_q_pow_neg_odd] -- new in this file
 242. [lw385_ai_zero_shift] -- new in this file
 243. [lw385_ai_delta_odd] -- new in this file
 244. [lw385_ai_mul_flip_aux] -- new in this file
 245. [lw385_ai_mul_flip] -- new in this file
 246. [lw385_qp_eval_q_wd] -- new in this file
 247. [lw385_pair_q_wd] -- new in this file
 248. [lw385_pair_abs_shore] -- new in this file
 249. [lw385_pair_flip_shore] -- new in this file
 250. [lw385_pair_flip_shore_mono] -- new in this file
 251. [lw0_ltT_leT_trans] -- new in this file
 252. [lw0_leT'_ltT_trans] -- new in this file
 253. [lw0_Qlt_le] -- new in this file
 254. [lw0_qmul_le0T] -- new in this file
 255. [lw0_qcompat4] -- new in this file
 256. [lw0_qcompat_r] -- new in this file
 257. [lw0_qcompat_l] -- new in this file
 258. [qltT_not_eq_zero] -- new in this file
 259. [qmult_ltT_0_compat] -- new in this file
 260. [lw0_q_pow_nonnegT] -- new in this file
 261. [lw0_q_of_nat_lt0T_S] -- new in this file
 262. [lw0_q_of_nat_lt0T] -- new in this file
 263. [lw0_mul_lt_one] -- new in this file
 264. [lw0_div_lt] -- new in this file
 265. [lw0_inv_le] -- new in this file
 266. [lw0_q_pow_mono_base] -- new in this file
 267. [lw0_q_fact_step] -- new in this file
 268. [lw0_fact_range] -- new in this file
 269. [lw0_q_fact_split] -- new in this file
 270. [lw0_fact_range_ge_pow] -- new in this file
 271. [lw0_q_pow_S] -- new in this file
 272. [lw0_q_fact_ne0] -- new in this file
 273. [lw0_Wb_nonneg] -- new in this file
 274. [lw0_Wb_ratio_eq] -- new in this file
 275. [lw0_frac_le] -- new in this file
 276. [lw0_lin_beat2] -- new in this file
 277. [lw0_lin_beat3] -- new in this file
 278. [lw0_twelve_AB_le] -- new in this file
 279. [lw0_Wb_ratio_bound] -- new in this file
 280. [lw0_Wb_seq_nonneg] -- new in this file
 281. [lw0_Wb_seq_decr] -- new in this file
 282. [altsum_qleT'_neg_le0] -- new in this file
 283. [altsum_qleT'_ge_sub] -- new in this file
 284. [altsum_acc] -- new in this file
 285. [altsum] -- new in this file
 286. [altsum_sgp] -- new in this file
 287. [altsum_acc_T] -- new in this file
 288. [altsum_acc_F] -- new in this file
 289. [altsum_acc_0_eq] -- new in this file
 290. [lw0_acc_add_gen] -- new in this file
 291. [lw0_altsum_add] -- new in this file
 292. [lw0_acc_quad] -- new in this file
 293. [lw0_pitS_q_pow_mul] -- new in this file
 294. [lw0_pitS_qmul_div_cancel] -- new in this file
 295. [lw0_pitS_div_lt_one] -- new in this file
 296. [lw0_pitS_pow_dec_helper] -- new in this file
 297. [lw0_pitS_pow_le_base] -- new in this file
 298. [lw0_pitS_Wbn0_scale_eq] -- new in this file
 299. [lw0_q_pow_add] -- new in this file
 300. [lw0_pitS_w0n_core] -- new in this file
 301. [lw0_pi_w0n_lt1] -- new in this file
 302. [leibsep_altsum_two_shore] -- new in this file
 303. [leibsep_w0n_xfer] -- new in this file
 304. [leibsep_w0n_step] -- new in this file
 305. [leibsep_w0n_pow] -- new in this file
 306. [leibsep_w0n_half] -- new in this file
 307. [qpoly_eval_mul] -- source: LW0PiIrrational.v@226
 308. [qpoly_deriv_iter_commute] -- source: LW0PiIrrational.v@381
 309. [lw0_q_fact_ge_one] -- source: LW0PiIrrational.v@470
 310. [lw0_q_fact_step2] -- source: LW0PiIrrational.v@482
 311. [lw0_q_pow_mult] -- source: LW0PiIrrational.v@1159
 312. [lw0_Qabs_pos_eq] -- source: LW0PiIrrational.v@1200
 313. [lw0_q_pow_one] -- source: LW0PiIrrational.v@1281
 314. [qpoly_opp] -- source: LW0PiIrrational.v@2491
 315. [lw0_mono] -- source: LW0PiIrrational.v@2874
 316. [lw0_qp_ai_mul_scalar_l] -- source: LW0PiIrrational.v@2939
 317. [lw0_qp_ai_mul_add_r] -- source: LW0PiIrrational.v@2967
 318. [lw0_qp_ai_mul_scalar_r] -- source: LW0PiIrrational.v@3001
 319. [lw0_qp_pair_add_r] -- source: LW0PiIrrational.v@3046
 320. [lw0_qp_pair_scalar_l] -- source: LW0PiIrrational.v@3062
 321. [lw0_qp_pair_scalar_r] -- source: LW0PiIrrational.v@3075
 322. [lw0_eval_opp] -- source: LW0PiIrrational.v@4508
 323. [lw0_Qmake_plus] -- source: LW0PiIrrational.v@4516
 324. [lw0_Qmake_succ] -- source: LW0PiIrrational.v@4525
 325. [lw0_coef_opp] -- source: LW0PiIrrational.v@4592
 326. [lw0_coef_iter_opp] -- source: LW0PiIrrational.v@4669
 327. [lw0_eval_at_zero] -- source: LW0PiIrrational.v@4684
 328. [lw0_eval_deriv_coef0] -- source: LW0PiIrrational.v@4689
 329. [lw0_eval_zero_coef] -- source: LW0PiIrrational.v@4706
 330. [lw0_eval_len_indep] -- source: LW0PiIrrational.v@4717
 331. [lw0_coef_iter_congr] -- source: LW0PiIrrational.v@4737
 332. [lw0_eval_iter_congr] -- source: LW0PiIrrational.v@4747
 333. [lw0_eval_deriv_iter_add] -- source: LW0PiIrrational.v@4758
 334. [lw0_eval_deriv_iter_scalar] -- source: LW0PiIrrational.v@4770
 335. [lw0_eval_iter_opp] -- source: LW0PiIrrational.v@4781
 336. [lw0_pred_iter] -- source: LW0PiIrrational.v@4796
 337. [lw0_shift_deriv] -- source: LW0PiIrrational.v@4802
 338. [lw0_qtail] -- source: LW0PiIrrational.v@4841
 339. [lw0_qtail_deriv_congr] -- source: LW0PiIrrational.v@4846
 340. [lw0_qtail_step] -- source: LW0PiIrrational.v@4873
 341. [lw0_coef_mul_mono_lt] -- source: LW0PiIrrational.v@4918
 342. [lw0_coef_mul_mono_ge] -- source: LW0PiIrrational.v@4943
 343. [lw0_qminus_pow] -- source: LW0PiIrrational.v@4966
 344. [lw0_niven_f_z] -- source: LW0PiIrrational.v@4976
 345. [lw0_niven_deriv_zero_0] -- source: LW0PiIrrational.v@4981
 346. [lw0_coef_mul_h0] -- source: LW0PiIrrational.v@4994
 347. [lw0_coef_mul_hS] -- new in this file
 348. [bpa_binom] -- source: UpReqBanachAdd.v@53
 349. [bpa_binom_pascal] -- source: UpReqBanachAdd.v@68
 350. [bpa_binom_0] -- source: UpReqBanachAdd.v@74
 351. [bpa_binom_out] -- source: UpReqBanachAdd.v@78
 352. [lw0_sub_succ_eq] -- new in this file
 353. [lw0_coef_qminus_pow] -- source: LW0PiIrrational.v@5042
 354. [lw0_ratio] -- source: LW0PiIrrational.v@5088
 355. [lw0_fact_ratio] -- source: LW0PiIrrational.v@5095
 356. [lw0_Qmake_mul] -- source: LW0PiIrrational.v@5119
 357. [lw0_qfact_Z] -- source: LW0PiIrrational.v@5122
 358. [lw0_binom] -- source: LW0PiIrrational.v@5162
 359. [lw0_binom_out] -- source: LW0PiIrrational.v@5184
 360. [lw0_zsign] -- source: LW0PiIrrational.v@5198
 361. [lw0_zsign_step] -- source: LW0PiIrrational.v@5204
 362. [lw0_z_lo] -- source: LW0PiIrrational.v@5212
 363. [lw0_z_hi] -- source: LW0PiIrrational.v@5237
 364. [lw0_qsum] -- source: LW0PiIrrational.v@5269
 365. [lw0_K_leg] -- source: LW0PiIrrational.v@5323
 366. [lw0_K] -- source: LW0PiIrrational.v@5329
 367. [lw0_pi_mono_eval] -- source: LW0PiIrrational.v@5468
 368. [lw0_pi_qminus_pow_eval] -- source: LW0PiIrrational.v@5485
 369. [Powpos] -- source: LW0PiIrrational.v@5952
 370. [lw0_posnat_zeq] -- source: LW0PiIrrational.v@5958
 371. [lw0_zpower_nat_add] -- source: LW0PiIrrational.v@5967
 372. [lw0_zpos_pospow] -- source: LW0PiIrrational.v@5976
 373. [lw0_q_pow_qmake] -- source: LW0PiIrrational.v@5985
 374. [lw0_q_pow_m1] -- source: LW0PiIrrational.v@5996
 375. [lw0_bpa_binom_eq] -- source: LW0PiIrrational.v@6009
 376. [lw0_sub_sub_shift] -- new in this file
 377. [lw0_conn_lo] -- source: LW0PiIrrational.v@6027
 378. [lw0_conn_hi] -- source: LW0PiIrrational.v@6063
 379. [lw0_alt_zsign] -- source: LW0PiIrrational.v@6319
 380. [lw0_pitB_ibp_dbl] -- source: LW0PiIrrational.v@6627
 381. [lw0_pitB_ai_mul01] -- source: LW0PiIrrational.v@6653
 382. [lw0_pitB_ai_mulA] -- source: LW0PiIrrational.v@6674
 383. [lw0_pitB_ai_monoL] -- source: LW0PiIrrational.v@6703
 384. [lw0_pitB_ai_pair2] -- source: LW0PiIrrational.v@6730
 385. [lw0_pitB_div_scale] -- source: LW0PiIrrational.v@6756
 386. [lw0_pitB_E] -- source: LW0PiIrrational.v@6768
 387. [lw0_pitB_ai_sin_aux] -- source: LW0PiIrrational.v@6829
 388. [lw0_pitB_ai_mul_sin_aux] -- source: LW0PiIrrational.v@6875
 389. [lw0_pitB_ai_mul_cons0] -- source: LW0PiIrrational.v@6919
 390. [lw0_pitB_ai_mul_cons1] -- source: LW0PiIrrational.v@6948
 391. [lw0_pitB_acc_S] -- source: LW0PiIrrational.v@6972
 392. [lw0_pitB_altsum_S] -- source: LW0PiIrrational.v@6995
 393. [lw0_pitB_q_pow_add] -- source: LW0PiIrrational.v@7005
 394. [lw0_pitB_Qeq_cancel_l] -- source: LW0PiIrrational.v@7016
 395. [lw0_pitB_bridge_aux] -- source: LW0PiIrrational.v@7032
 396. [lw0_pitB_bridge] -- source: LW0PiIrrational.v@7138
 397. [lw0_pitB_conv_lw0_succ] -- source: LW0PiIrrational.v@7231
 398. [lw0_pitB_conv_mult_le_l] -- source: LW0PiIrrational.v@7240
 399. [lw0_pitB_conv_pow2_ge] -- source: LW0PiIrrational.v@7250
 400. [lw0_pitB_conv_half_le1] -- source: LW0PiIrrational.v@7284
 401. [lw0_pitB_conv_half_mono] -- source: LW0PiIrrational.v@7296
 402. [lw0_pitB_conv_div_mul_cancel] -- source: LW0PiIrrational.v@7354
 403. [lw0_pitB_conv_geomscale] -- source: LW0PiIrrational.v@7367
 404. [lw0_pitB_conv_qabs_pow] -- source: LW0PiIrrational.v@7424
 405. [lw0_pitB_conv_t_nonneg] -- source: LW0PiIrrational.v@7445
 406. [lw0_pitB_conv_tstep] -- source: LW0PiIrrational.v@7456
 407. [lw0_pitB_conv_half_iter] -- source: LW0PiIrrational.v@7799
 408. [lw0_pitB_conv_qthr] -- source: LW0PiIrrational.v@7837
 409. [lw0_pitB_conv_qeqL_ltT] -- source: LW0PiIrrational.v@7930
 410. [lw0_pitB_conv_qeqR_ltT] -- source: LW0PiIrrational.v@7939
 411. [lw0_pitB_conv_t_vanish] -- source: LW0PiIrrational.v@7948
 412. [lw0_pitB_conv_pwi] -- source: LW0PiIrrational.v@8539
 413. [lw0_pitB_conv_pwi_scalar] -- source: LW0PiIrrational.v@8554
 414. [lw0_pitB_conv_pwi_add_le] -- source: LW0PiIrrational.v@8585
 415. [lw0_pitB_conv_pwi_mul_le] -- source: LW0PiIrrational.v@8649
 416. [lw0_pitB_conv_pwi_ai_le] -- source: LW0PiIrrational.v@8681
 417. [lw0_pitB_conv_pair_vanish] -- source: LW0PiIrrational.v@8745
 418. [lw0_pi_qeq_ltT_r] -- source: LW0PiIrrational.v@9709
 419. [lw0_pitB_pair_rtail] -- source: LW0PiIrrational.v@10001
 420. [lw0_pitB_pair_rtail_vanish_gap] -- source: LW0PiIrrational.v@10026
 421. [lw0_add_nil_r] -- source: LW0PiIrrational.v@10290
 422. [lw0_mul_nil_r_coef] -- source: LW0PiIrrational.v@10298
 423. [lw0_mul_scalar_left] -- source: LW0PiIrrational.v@10312
 424. [lw0_mul_add_left] -- source: LW0PiIrrational.v@10332
 425. [lw0_mul_cons0_left] -- source: LW0PiIrrational.v@10359
 426. [lw0_mul_assoc] -- source: LW0PiIrrational.v@10371
 427. [lw0_mul_unit_right] -- source: LW0PiIrrational.v@10403
 428. [lw0_mul_cons0_right] -- source: LW0PiIrrational.v@10418
 429. [lw0_mul_comm] -- source: LW0PiIrrational.v@10438
 430. [lw0_lintail_qtail] -- source: LW0PiIrrational.v@10470
 431. [lw0_cons0_congr] -- source: LW0PiIrrational.v@10485
 432. [lw0_pi_mono_cons0] -- source: LW0PiIrrational.v@10495
 433. [lw0_pi_qminus_qtail] -- source: LW0PiIrrational.v@10507
 434. [lw0_mul_tshift] -- source: LW0PiIrrational.v@10515
 435. [lw0_qtail_eval_0] -- source: LW0PiIrrational.v@10526
 436. [lw0_deriv_iter_one] -- source: LW0PiIrrational.v@10542
 437. [lw0_alt_double] -- source: LW0PiIrrational.v@10556
 438. [lw0_q_pow_m0] -- source: LW0PiIrrational.v@10567
 439. [lw0_pi_mirror_bnd] -- source: LW0PiIrrational.v@10580
 440. [lw0_niven_mirror] -- source: LW0PiIrrational.v@10619
 441. [lw0_niven_deriv_mirror_even] -- source: LW0PiIrrational.v@10689
 442. [lw0_coef_mul_congr] -- source: LW0PiIrrational.v@10750
 443. [lw0_pi_qminus_z_bridge] -- source: LW0PiIrrational.v@10768
 444. [lw0_pi_mono_z_bridge] -- source: LW0PiIrrational.v@10780
 445. [lw0_q_pow_one_base] -- source: LW0PiIrrational.v@10791
 446. [lw0_niven_scalar_bridge] -- source: LW0PiIrrational.v@10805
 447. [lw0_niven_pi_z_bridge] -- source: LW0PiIrrational.v@10832
 448. [lw0_niven_deriv_zero_0_ab] -- source: LW0PiIrrational.v@10852
 449. [lw0_niven_deriv_conn_lo_ab] -- source: LW0PiIrrational.v@10863
 450. [lw0_niven_deriv_conn_hi_ab] -- source: LW0PiIrrational.v@10875
 451. [lw0_F_eval_qsum] -- source: LW0PiIrrational.v@10887
 452. [lw0_qsum_ext2] -- source: LW0PiIrrational.v@10903
 453. [lw0_K_closure_F0Fq] -- source: LW0PiIrrational.v@10916
 454. [lw0_pitB_pair_rtail_vanish_hpair] -- source: LW0PiIrrational.v@10976
 455. [lw0_pitB_pair_conv_f] -- source: LW0PiIrrational.v@11840
 456. [lw0_pitB_pair_conv_delta] -- source: LW0PiIrrational.v@11851
 457. [lw0_pitB_pair_conv_delta'] -- source: LW0PiIrrational.v@11856
 458. [lw0_qpoly_eqT_of_prop] -- source: LW0PiIrrational.v@11865
 459. [lw0_qpoly_eq_prop_of_eqT] -- source: LW0PiIrrational.v@11871
 460. [lw0_qpoly_eqT_refl] -- source: LW0PiIrrational.v@11877
 461. [lw0_qpoly_eqT_sym] -- source: LW0PiIrrational.v@11882
 462. [lw0_qpoly_eqT_trans] -- source: LW0PiIrrational.v@11889
 463. [lw0_qpoly_eqT_add] -- source: LW0PiIrrational.v@11898
 464. [lw0_qpoly_eqT_cons_congr] -- source: LW0PiIrrational.v@11908
 465. [lw0_pitB_pair_conv_scalar_congr] -- source: LW0PiIrrational.v@11919
 466. [lw0_pitB_pair_conv_mul_r] -- source: LW0PiIrrational.v@11927
 467. [lw0_pitB_pair_conv_coef_ai] -- source: LW0PiIrrational.v@11959
 468. [lw0_pitB_pair_conv_ai_congr] -- source: LW0PiIrrational.v@11974
 469. [lw0_pitB_pair_conv_pair_congr_r] -- source: LW0PiIrrational.v@11984
 470. [lw0_pitB_pair_conv_zshift_bridge] -- source: LW0PiIrrational.v@12013
 471. [lw0_pitB_pair_conv_delta_br] -- source: LW0PiIrrational.v@12024
 472. [lw0_pitB_pair_conv_sin_aux_hi] -- source: LW0PiIrrational.v@12033
 473. [lw0_pitB_pair_conv_sin_aux_lo] -- source: LW0PiIrrational.v@12055
 474. [lw0_pitB_pair_conv_qdiv_mult_inv] -- source: LW0PiIrrational.v@12097
 475. [lw0_pitB_pair_conv_sin_inc] -- source: LW0PiIrrational.v@12102
 476. [lw0_pitB_pair_conv_qabs_sign1] -- source: LW0PiIrrational.v@12152
 477. [lw0_pitB_pair_conv_sig2] -- source: LW0PiIrrational.v@12162
 478. [lw0_pitB_pair_conv_sinc] -- source: LW0PiIrrational.v@12182
 479. [lw0_pitB_pair_conv_core] -- source: LW0PiIrrational.v@12216
 480. [lw0_pitB_pair_conv_qabs_canon] -- source: LW0PiIrrational.v@12262
 481. [lw0_pitB_pair_conv_qabs_wd] -- source: LW0PiIrrational.v@12277
 482. [lw0_pitB_conv_pwi_shift1_eq] -- source: LW0PiIrrational.v@12300
 483. [lw0_pitB_conv_pwi_zero_shift_eq] -- source: LW0PiIrrational.v@12314
 484. [lw0_pitB_conv_div_den_mono] -- source: LW0PiIrrational.v@12337
 485. [lw0_pitB_conv_pwi_k_mono] -- source: LW0PiIrrational.v@12382
 486. [lw0_pitB_conv_pwi_add_k_mono] -- source: LW0PiIrrational.v@12426
 487. [lw0_pitB_conv_pwi_nonneg] -- source: LW0PiIrrational.v@12443
 488. [lw0_pitB_conv_pwi_one_eq] -- source: LW0PiIrrational.v@12474
 489. [lw0_pitB_conv_pwi_muliter] -- source: LW0PiIrrational.v@12489
 490. [lw0_pitB_conv_pwi_mul_le_iter] -- source: LW0PiIrrational.v@12497
 491. [lw0_pitB_conv_pwi_shift_one_domin] -- source: LW0PiIrrational.v@12524
 492. [lw0_pitB_conv_pwi_muliter_scalar] -- source: LW0PiIrrational.v@12543
 493. [lw0_pitB_conv_pwi_muliter_shift] -- source: LW0PiIrrational.v@12571
 494. [lw0_pitB_conv_pwi_muliter_eq] -- source: LW0PiIrrational.v@12615
 495. [lw0_pitB_conv_pwi_mul_shift_domin] -- source: LW0PiIrrational.v@12636
 496. [lw0_pitB_conv_pair_deltamul_weight] -- source: LW0PiIrrational.v@12672
 497. [lw0_pitB_conv_pair_vanish_deltam] -- source: LW0PiIrrational.v@12752
 498. [lw0_pitB_pair_conv] -- source: LW0PiIrrational.v@13267
 499. [lw0_pitB_pair_rtail_vanish] -- new in this file
 500. [lw0_z_lo_integer] -- new in this file
 501. [lw0_z_hi_integer] -- new in this file
 502. [lw0_sigT_plus] -- new in this file
 503. [lw0_sigT_Zscale] -- new in this file
 504. [lw0_qsum_integer] -- new in this file
 505. [lw0_K_leg_integer] -- new in this file
 506. [lw0_K_integer] -- new in this file
 507. [lw0_pi_contra_gate] -- new in this file
 508. [leibsep_abs3_split] -- new in this file
 509. [lw0_pitB_pair_telescope] -- new in this file
 510. [leibsep_pair_slack_bound] -- new in this file
 511. [leibsep_G4c_pair_slack_window_from] -- new in this file
 512. [leibsep_beta_contra] -- new in this file
 513. [leibsep_false_branch_contra] -- new in this file
 514. [leibsep_gate_open] -- source: LW0LeibSeparation.v@53
 515. [leibsep_gate_open_true] -- source: LW0LeibSeparation.v@182
 516. [lw0m_tail_bounded_pi] -- new in this file (internal design ledger)
 517. [leibsep_q_kernel_guarded] -- source: LW0LeibSeparation.v@220
 518. [leibsep_gate_open_false] -- new in this file
 519. [leibsep_closedband_of_gate_false] -- new in this file
 520. [leibsep_shore_q_le_ten_thirds] -- new in this file (internal design ledger)
 521. [leibsep_shore_q_pos] -- new in this file (internal design ledger)
 522. [leibsep_q_kernel_gate_carrier] -- source: LW0LeibSeparation.v@3928
 523. [piL_q_pow_0] -- new in this file (internal design ledger)
 524. [piL_q_fact_0] -- new in this file (internal design ledger)
 525. [piL_qdiv_1_r] -- new in this file (internal design ledger)
 526. [piL_sin_term_0] -- new in this file (internal design ledger)
 527. [piL_cos_term_0] -- new in this file (internal design ledger)
 528. [piL_sin_term_congr] -- new in this file (internal design ledger)
 529. [piL_cos_term_congr] -- new in this file (internal design ledger)
 530. [piL_sin_partial_congr] -- new in this file (internal design ledger)
 531. [piL_cos_partial_congr] -- new in this file (internal design ledger)
 532. [piL_sin_dres] -- source: S12_B5RecycleSF.v@8294
 533. [piL_sin_partial_double] -- new in this file (internal design ledger)
 534. [piL_sin_partial_double_at] -- new in this file (internal design ledger)
 535. [piL_cos_dres] -- source: S12_B5RecycleSF.v@8315
 536. [piL_cos_partial_double] -- new in this file (internal design ledger)
 537. [piL_pyth_dres] -- source: S12_B5RecycleSF.v@8138
 538. [piL_pythag_partial] -- new in this file (internal design ledger)
 539. [piL_quad_dres] -- source: S12_B5RecycleSF.v@8122
 540. [piL_sin_partial_quad] -- new in this file (internal design ledger)
 541. [piL_cos_quad_dres] -- source: S12_B5RecycleSF.v@8299
 542. [piL_cos_partial_quad] -- new in this file (internal design ledger)
 543. [piL_quad_vertex_factor] -- new in this file (internal design ledger)
 544. [piL_sin_quad_xL] -- new in this file (internal design ledger)
 545. [piL_cos_quad_xL] -- new in this file (internal design ledger)
 546. [piL_qabs_zero] -- new in this file (internal design ledger)
 547. [piL_qabs_two] -- new in this file (internal design ledger)
 548. [piL_qabs_four] -- new in this file (internal design ledger)
 549. [piL_qle_0_two] -- new in this file (internal design ledger)
 550. [piL_qle_0_four] -- new in this file (internal design ledger)
 551. [piL_mult_le_l] -- new in this file (internal design ledger)
 552. [piL_abs_div_pos_den] -- new in this file (internal design ledger)
 553. [piL_leT'_eq_intro_l] -- new in this file (internal design ledger)
 554. [piL_leT'_eq_intro_r] -- new in this file (internal design ledger)
 555. [piL_abs_mult_le] -- new in this file (internal design ledger)
 556. [piL_abs_coeff2_2] -- new in this file (internal design ledger)
 557. [piL_abs_coeff4_3] -- new in this file (internal design ledger)
 558. [piL_abs2_plus_le] -- new in this file (internal design ledger)
 559. [piL_abs3_plus_le] -- new in this file (internal design ledger)
 560. [piL_abs4_plus_le] -- new in this file (internal design ledger)
 561. [piL_abs_opp_le] -- new in this file (internal design ledger)
 562. [piL_abs2_le] -- new in this file (internal design ledger)
 563. [piL_qltT_0_double] -- new in this file (internal design ledger)
 564. [piL_sin_term_abs_bound] -- new in this file (internal design ledger)
 565. [piL_cos_term_abs_bound] -- new in this file (internal design ledger)
 566. [piL_sin_partial_abs_bound] -- new in this file (internal design ledger)
 567. [piL_cos_partial_abs_bound] -- new in this file (internal design ledger)
 568. [piL_dres_majorant] -- new in this file (internal design ledger)
 569. [piL_cos_dres_majorant] -- new in this file (internal design ledger)
 570. [piL_quad_dres_majorant] -- new in this file (internal design ledger)
 571. [piL_sin_dres_majorant_bound] -- new in this file (internal design ledger)
 572. [piL_cos_dres_majorant_bound] -- new in this file (internal design ledger)
 573. [piL_quad_dres_majorant_bound] -- new in this file (internal design ledger)
 574. [piLred_qle_wd_l] -- new in this file (internal design ledger)
 575. [piLred_qle_wd_r] -- new in this file (internal design ledger)
 576. [piLred_abs_mult] -- new in this file (internal design ledger)
 577. [piLred_abs_CmS_le] -- new in this file (internal design ledger)
 578. [piLred_vtx_anchor_xL] -- new in this file (internal design ledger)
 579. [d3p_inject_nat] -- new in this file
 580. [d3p_inject_add] -- new in this file (internal design ledger)
 581. [d3p_inject_mul] -- new in this file (internal design ledger)
 582. [d3p_inject_succ] -- new in this file (internal design ledger)
 583. [d3p_inject_mono] -- new in this file (internal design ledger)
 584. [d3p_inject_ceiling_ge] -- new in this file (internal design ledger)
 585. [d3p_nat_pow2_ge_succ] -- new in this file (internal design ledger)
 586. [d3p_q_pow_0_succ] -- new in this file (internal design ledger)
 587. [d3p_q_pow_add] -- new in this file (internal design ledger)
 588. [d3p_q_fact_step] -- new in this file (internal design ledger)
 589. [d3p_q_pow_quarter_step] -- new in this file (internal design ledger)
 590. [d3p_q_pow_quarter_antitone] -- new in this file (internal design ledger)
 591. [d3p_mult_le_r_pos] -- new in this file (internal design ledger)
 592. [d3p_qdiv_mul_r] -- new in this file (internal design ledger)
 593. [d3p_qmult_neq0] -- new in this file (internal design ledger)
 594. [d3p_fact_dom_pow] -- new in this file
 595. [d3p_sin_term] -- new in this file
 596. [d3p_cos_term] -- new in this file
 597. [d3p_q_pow_pos] -- new in this file (internal design ledger)
 598. [d3p_inject_pos] -- new in this file (internal design ledger)
 599. [d3p_sin_term_pos] -- new in this file (internal design ledger)
 600. [d3p_sin_term_nonneg] -- new in this file (internal design ledger)
 601. [d3p_cos_term_nonneg] -- new in this file (internal design ledger)
 602. [d3p_cos_term_pos] -- new in this file (internal design ledger)
 603. [d3p_two_le_inject] -- new in this file (internal design ledger)
 604. [d3p_B_le_two_inject] -- new in this file (internal design ledger)
 605. [d3p_sin_term_quarter] -- new in this file
 606. [d3p_cos_term_quarter] -- new in this file (internal design ledger)
 607. [d3p_sin_term_iter] -- new in this file (internal design ledger)
 608. [d3p_cos_term_iter] -- new in this file (internal design ledger)
 609. [d3p_sin_powtail] -- new in this file
 610. [d3p_cos_powtail] -- new in this file
 611. [d3p_sin_powtail_zero] -- new in this file (internal design ledger)
 612. [d3p_cos_powtail_zero] -- new in this file (internal design ledger)
 613. [d3p_sin_powtail_quarter] -- new in this file (internal design ledger)
 614. [d3p_cos_powtail_quarter] -- new in this file (internal design ledger)
 615. [d3p_qlt_plus_1] -- new in this file (internal design ledger)
 616. [d3p_quarter_pow_lt] -- new in this file (internal design ledger)
 617. [d3p_sin_partial_step] -- new in this file
 618. [d3p_cos_partial_step] -- new in this file (internal design ledger)
 619. [d3p_sub_add_eq] -- new in this file (internal design ledger)
 620. [d3p_sin_partial_tail_abs] -- new in this file (internal design ledger)
 621. [d3p_cos_partial_tail_abs] -- new in this file (internal design ledger)
 622. [d3p_abssum_mono] -- new in this file (internal design ledger)
 623. [d3p_abssum_cos_mono] -- new in this file (internal design ledger)
 624. [d3p_sin_term_dec] -- new in this file (internal design ledger)
 625. [d3p_sin_partial_cauchy] -- new in this file (internal design ledger)
 626. [d3p_cos_partial_cauchy] -- new in this file (internal design ledger)
 627. [piLd3_lp_odd_nonneg] -- new in this file
 628. [piLd3_u_abs_le_s6] -- new in this file
 629. [piLd3_lp_a6_pos] -- new in this file
 630. [piLd3_s6_pos] -- new in this file
 631. [piLd3_qlt_add_r] -- new in this file
 632. [piLd3_c16_pos] -- new in this file (internal design ledger)
 633. [piLd3_c32_pos] -- new in this file
 634. [piLd3_seed_halfwin] -- new in this file
 635. [piLd3_seed_dres] -- new in this file
 636. [piLd3_seed_dcos] -- new in this file
 637. [piLd3_B] -- new in this file (internal design ledger)
 638. [piLd3_B_pos] -- new in this file (internal design ledger)
 639. [piLd3_abs_2u_le_B] -- new in this file
 640. [piLd3_sin_xL_eq] -- new in this file
 641. [piLd3_cos_xL_plus1_eq] -- new in this file
 642. [piLd3_abs_S_le] -- new in this file
 643. [piLd3_abs_Splus_le] -- new in this file
 644. [piLd3_halfsq_bound] -- new in this file
 645. [piLd3_dpit_bound] -- new in this file
 646. [piLd3_qle_0_mult2] -- new in this file
 647. [piLd3_mult2_le] -- new in this file
 648. [piLd3_qle_0_plus1] -- new in this file
 649. [piLd3_2SC_le] -- new in this file
 650. [piLd3_sin_bound] -- new in this file
 651. [piLd3_cos_bound] -- new in this file
 652. [piLd3_Hc1] -- new in this file (internal design ledger)
 653. [piLd3_Hc32] -- new in this file (internal design ledger)
 654. [piLd3_H82] -- new in this file (internal design ledger)
 655. [piLd3_H328] -- new in this file (internal design ledger)
 656. [piLd3_H412] -- new in this file
 657. [piLd3_budget_v1] -- new in this file
 658. [piLd3_budget_v2] -- new in this file
 659. [piLd3_sin_xL_vanish_carry] -- new in this file
 660. [piL_sin_xL_vanish] -- new in this file
 661. [piLd3_cos_xL_vanish_carry] -- new in this file
 662. [piL_cos_xL_neg1_vanish] -- new in this file (internal design ledger)
 663. [lw0_pitB_conv_m1_cases] -- new in this file
 664. [lw0_pitB_conv_cos_term_abs] -- new in this file
 665. [lw0_pitB_conv_tail_gen] -- new in this file
 666. [lw0_pitB_conv_cos_tail] -- new in this file
 667. [leibsep_cos_qp_deriv_tail_stable] -- new in this file
 668. [leibsep_ratio_slot] -- new in this file
 669. [lw0_pitB_conv_sin_term_abs] -- new in this file
 670. [lw0_pitB_conv_sin_tail] -- new in this file
 671. [leibsep_sin_qp_tail_stable] -- new in this file
 672. [lw62_qdiv_nonneg] -- new in this file
 673. [lw95_mul0] -- new in this file
 674. [lw95_qpow_nonneg] -- new in this file
 675. [lw1131_abssum_cos_nonneg] -- new in this file
 676. [lw62_qpow_abs] -- new in this file
 677. [lw62_cos_term_dom] -- new in this file
 678. [lw62_abssum_cos_dom] -- new in this file
 679. [lw62_abssum_S] -- new in this file
 680. [lw62_qdiv_den_id] -- new in this file
 681. [lw62_qdiv_le] -- new in this file
 682. [lw95_qfact_mono] -- new in this file
 683. [lw95_qfact_le] -- new in this file
 684. [lw62_abssum_cos_le] -- new in this file
 685. [lw62_zsquare_nonneg] -- new in this file
 686. [lw62_sq_nonneg] -- new in this file
 687. [lw62_qpow_even_nonneg] -- new in this file
 688. [lw62_abssum_step_mono] -- new in this file
 689. [lw62_abssum_mono] -- new in this file
 690. [lw62_q30_pos] -- new in this file
 691. [lw95_mul_le_compat] -- new in this file
 692. [lw62_georatio] -- new in this file
 693. [lw62_qpow_add] -- new in this file
 694. [lw65_qdiv_le_prod] -- new in this file
 695. [lw65_qpow_inv_pair] -- new in this file
 696. [lw65_qpow_mul] -- new in this file
 697. [lw62_item_dom] -- new in this file
 698. [lw62_rsum] -- new in this file
 699. [lw62_abssum_shift] -- new in this file
 700. [lw62_qinv30_pos] -- new in this file
 701. [lw62_rsum_nonneg] -- new in this file
 702. [lw62_rsum_tele] -- new in this file
 703. [lw62_abssum_env] -- new in this file
 704. [lw62_abssum_nonneg] -- new in this file
 705. [lw62_abssum_cos_env] -- new in this file
 706. [qltw_pc_pw] -- new in this file
 707. [qltw_pw_pc] -- new in this file
 708. [leibsep_Wb01_diff_lower] -- new in this file
 709. [lw1131_C_le_eps0K] -- new in this file
 710. [lw1190_div_mul_cancel] -- new in this file
 711. [tsl] -- new in this file
 712. [tcl] -- new in this file
 713. [sin_slot_eps0] -- new in this file
 714. [cos_slot_eps0] -- new in this file
 715. [tqF] -- new in this file
 716. [tslF] -- new in this file
 717. [tclF] -- new in this file
 718. [caps_scaled] -- new in this file
 719. [leibsep_q_kernel] -- new in this file
*)
```

## PiWindowCore.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiWindowCore.v] lines 1539-1655.

```coq
(* Statement provenance: for every statement of this file, the
   source statement of this development that it was migrated from,
   with the source coordinates.  Rows marked (new) are statements
   first stated in this file.

   [Id] <- [Id] at [S01_BaseRing.v:L41-L43]
   [id_trans] <- [id_trans] at [S01_BaseRing.v:L59-L62]
   [Qlt_bool] <- [Qlt_bool] at [S02_CauchyComplete.v:L42-L47]
   [QltT] <- [QltT] at [S02_CauchyComplete.v:L48]
   [QleT'] <- [QleT'] at [S02_CauchyComplete.v:L99]
   [qltw_S02_Qlt_bool] <- [Qlt_bool] (restated as [qltw_S02_Qlt_bool]) at [S02_CauchyComplete.v:L42-L47]
   [qltw_S02_Qle_bool] <- [Qle_bool] (restated as [qltw_S02_Qle_bool]) at [S02_CauchyComplete.v:L92-L96]
   [qltw_Qlt_bool_Qcompare] <- (new in this file)
   [qltw_Qle_bool_Qcompare] <- (new in this file)
   [qltw_Qeq_bool_Qcompare] <- (new in this file)
   [qltw_Qlt_bool_orig] <- (new in this file)
   [qltw_Qle_bool_orig] <- (new in this file)
   [qltw_QltT_orig] <- (new in this file)
   [qltw_S02_QltT] <- (new in this file)
   [qltw_QleT'_orig] <- (new in this file)
   [qltw_S02_QleT'] <- (new in this file)
   [qltw_samp_QltT_0_1] <- (new in this file)
   [qltw_samp_QleT'_1_1] <- (new in this file)
   [qltw_samp_Qeq_bool_2_2] <- (new in this file)
   [leiblw_id_eq] <- [leiblw_id_eq] at [LW0LeibWindow.v:L65-L66]
   [leiblw_id_inv] <- [leiblw_id_inv] at [LW0LeibWindow.v:L68-L69]
   [QltT_to_Qlt] <- [QltT_to_Qlt] at [S02_CauchyComplete.v:L51-L58]
   [Qlt_to_QltT] <- [Qlt_to_QltT] at [S02_CauchyComplete.v:L60-L80]
   [QleT'_to_Qle] <- [QleT'_to_Qle] at [S02_CauchyComplete.v:L103-L112]
   [Qle_to_QleT'] <- [Qle_to_QleT'] at [S02_CauchyComplete.v:L115-L122]
   [leiblw_even] <- [leiblw_even] at [LW0LeibWindow.v:L32-L36]
   [leiblw_even_2m] <- [leiblw_even_2m] at [LW0LeibWindow.v:L38-L43]
   [leiblw_even_2m1] <- [leiblw_even_2m1] at [LW0LeibWindow.v:L45-L49]
   [leiblw_par_decomp] <- [leiblw_par_decomp] at [LW0LeibWindow.v:L52-L60]
   [leiblw_znat_pos] <- [leiblw_znat_pos] at [LW0LeibWindow.v:L94-L98]
   [leiblw_pos_succ] <- [leiblw_pos_succ] at [LW0LeibWindow.v:L101-L105]; source at [LW0LeibWindow.v:L108-L110]
   [leiblw_pos_succ1] <- [leiblw_pos_succ1] at [LW0LeibWindow.v:L113-L114]
   [leiblw_qmake_eq] <- [leiblw_qmake_eq] at [LW0LeibWindow.v:L116-L120]
   [leiblw_qmake_lt] <- [leiblw_qmake_lt] at [LW0LeibWindow.v:L122-L128]
   [leiblw_qmake_le] <- [leiblw_qmake_le] at [LW0LeibWindow.v:L130-L136]
   [leiblw_qabs_id] <- [leiblw_qabs_id] at [LW0LeibWindow.v:L138-L145]
   [leiblw_qabs_neg] <- [leiblw_qabs_neg] at [LW0LeibWindow.v:L147-L154]
   [leiblw_t] <- [leiblw_t] at [LW0LeibWindow.v:L160-L163]
   [leiblw_S] <- [leiblw_S] at [LW0LeibWindow.v:L165-L169]
   [leiblw_S_SS] <- [leiblw_S_SS] at [LW0LeibWindow.v:L171-L173]
   [leiblw_S_step] <- [leiblw_S_step] at [LW0LeibWindow.v:L175-L176]
   [leiblw_t_pos_case] <- [leiblw_t_pos_case] at [LW0LeibWindow.v:L178-L180]
   [leiblw_t_neg_case] <- [leiblw_t_neg_case] at [LW0LeibWindow.v:L182-L184]
   [leiblw_t_even] <- [leiblw_t_even] at [LW0LeibWindow.v:L186-L191]
   [leiblw_t_odd] <- [leiblw_t_odd] at [LW0LeibWindow.v:L193-L198]
   [leiblw_t_even_pos] <- [leiblw_t_even_pos] at [LW0LeibWindow.v:L200-L205]
   [leiblw_t_odd_neg] <- [leiblw_t_odd_neg] at [LW0LeibWindow.v:L207-L211]
   [leiblw_qplus_norm] <- [leiblw_qplus_norm] at [LW0LeibWindow.v:L218-L223]
   [leiblw_qplus_lt0] <- [leiblw_qplus_lt0] at [LW0LeibWindow.v:L225-L230]
   [leiblw_qplus_lt0b] <- [leiblw_qplus_lt0b] at [LW0LeibWindow.v:L232-L238]
   [leiblw_qplus_le0] <- [leiblw_qplus_le0] at [LW0LeibWindow.v:L240-L245]
   [leiblw_qplus_eq] <- [leiblw_qplus_eq] at [LW0LeibWindow.v:L247-L253]
   [leiblw_qopp_distr] <- [leiblw_qopp_distr] at [LW0LeibWindow.v:L255-L258]
   [leiblw_qneg_plus_eq] <- [leiblw_qneg_plus_eq] at [LW0LeibWindow.v:L261-L268]
   [leiblw_qshunt] <- [leiblw_qshunt] at [LW0LeibWindow.v:L271-L281]
   [leiblw_qplus_opp_l0] <- [leiblw_qplus_opp_l0] at [LW0LeibWindow.v:L283-L284]
   [leiblw_qshunt_neg] <- [leiblw_qshunt_neg] at [LW0LeibWindow.v:L287-L292]
   [leiblw_qopp_lt] <- [leiblw_qopp_lt] at [LW0LeibWindow.v:L294-L297]
   [leiblw_qminus_flip] <- [leiblw_qminus_flip] at [LW0LeibWindow.v:L299-L300]
   [leiblw_qle_add_r] <- [leiblw_qle_add_r] at [LW0LeibWindow.v:L302-L303]
   [leiblw_qle_add2_r] <- [leiblw_qle_add2_r] at [LW0LeibWindow.v:L305-L310]
   [leiblw_qle_add_l] <- [leiblw_qle_add_l] at [LW0LeibWindow.v:L312-L313]
   [leiblw_qplus_le0b] <- [leiblw_qplus_le0b] at [LW0LeibWindow.v:L315-L320]
   [leiblw_zpos_mul] <- [leiblw_zpos_mul] at [LW0LeibWindow.v:L322-L327]
   [leiblw_step_even_pos] <- [leiblw_step_even_pos] at [LW0LeibWindow.v:L333-L347]
   [leiblw_step_odd_neg] <- [leiblw_step_odd_neg] at [LW0LeibWindow.v:L349-L365]
   [leiblw_interlace] <- [leiblw_interlace] at [LW0LeibWindow.v:L367-L377]
   [leiblw_mono_even] <- [leiblw_mono_even] at [LW0LeibWindow.v:L379-L402]
   [leiblw_mono_odd] <- [leiblw_mono_odd] at [LW0LeibWindow.v:L404-L427]
   [leiblw_gap] <- [leiblw_gap] at [LW0LeibWindow.v:L433-L434]
   [leiblw_gap_pos] <- [leiblw_gap_pos] at [LW0LeibWindow.v:L436-L437]
   [leiblw_gap_even_step] <- [leiblw_gap_even_step] at [LW0LeibWindow.v:L439-L461]
   [leiblw_gap_odd_step] <- [leiblw_gap_odd_step] at [LW0LeibWindow.v:L463-L489]
   [leiblw_lower_even_e] <- [leiblw_lower_even_e] at [LW0LeibWindow.v:L601-L609]
   [leiblw_lower_even_o] <- [leiblw_lower_even_o] at [LW0LeibWindow.v:L612-L623]
   [leiblw_lower_odd_e] <- [leiblw_lower_odd_e] at [LW0LeibWindow.v:L626-L638]
   [leiblw_lower_odd_o] <- [leiblw_lower_odd_o] at [LW0LeibWindow.v:L641-L649]
   [leiblw_dist] <- [leiblw_dist] at [LW0LeibWindow.v:L652-L719]
   [leiblw_dist_set] <- [leiblw_dist_set] at [LW0LeibWindow.v:L747-L754]
   [leiblw_zf] <- [leiblw_zf] at [LW0LeibWindow.v:L495-L500]
   [leiblw_qf] <- [leiblw_qf] at [LW0LeibWindow.v:L501-L502]
   [leiblw_zf_S] <- (new in this file)
   [leiblw_zf_ge1] <- [leiblw_zf_ge1] at [LW0LeibWindow.v:L503-L504]
   [leiblw_zf_ge_id] <- [leiblw_zf_ge_id] at [LW0LeibWindow.v:L506-L513]
   [leiblw_zf_lower] <- [leiblw_zf_lower] at [LW0LeibWindow.v:L515-L526]
   [leiblw_zf_2n1] <- [leiblw_zf_2n1] at [LW0LeibWindow.v:L528-L533]
   [leiblw_zf_2n3] <- [leiblw_zf_2n3] at [LW0LeibWindow.v:L536-L543]
   [leiblw_integrality] <- [leiblw_integrality] at [LW0LeibWindow.v:L546-L597]
   [leiblw_margin] <- [leiblw_margin] at [LW0LeibWindow.v:L761-L762]
   [leiblw_natwin] <- [leiblw_natwin] at [LW0LeibWindow.v:L769-L770]
   [leiblw_qabs_make] <- [leiblw_qabs_make] at [LW0LeibWindow.v:L772-L773]
   [leiblw_natwin_residual] <- [leiblw_natwin_residual] at [LW0LeibWindow.v:L777-L789]
   [leiblw_natwin_ge] <- [leiblw_natwin_ge] at [LW0LeibWindow.v:L791-L798]
   [leiblw_zle_mul1] <- (new in this file)
   [leiblw_natwin_mono] <- [leiblw_natwin_mono] at [LW0LeibWindow.v:L800-L814]
   [leiblw_S1_4] <- [leiblw_S1_4] at [LW0LeibWindow.v:L816-L817]
   [leiblw_S_le4] <- [leiblw_S_le4] at [LW0LeibWindow.v:L819-L838]
   [leiblw_S_ge0] <- [leiblw_S_ge0] at [LW0LeibWindow.v:L840-L852]
   [leiblw_qabs_bound] <- [leiblw_qabs_bound] at [LW0LeibWindow.v:L854-L860]
   [leiblw_natwin_unbounded] <- [leiblw_natwin_unbounded] at [LW0LeibWindow.v:L894-L908]
   [leiblw_margin_unbounded] <- [leiblw_margin_unbounded] at [LW0LeibWindow.v:L910-L921]
   [leiblw_nivwin] <- [leiblw_nivwin] at [LW0LeibWindow.v:L959-L960]
   [leiblw_nivwin_bounded] <- [leiblw_nivwin_bounded] at [LW0LeibWindow.v:L962-L966]
   [leiblw_family_separation] <- [leiblw_family_separation] at [LW0LeibWindow.v:L971-L978]
   [leiblw_pof] <- [leiblw_pof] at [LW0LeibWindow.v:L1030-L1041]
   [leiblw_div2_even] <- [leiblw_div2_even] at [LW0LeibWindow.v:L1043-L1045]
   [leiblw_div2_odd] <- [leiblw_div2_odd] at [LW0LeibWindow.v:L1048-L1050]
   [leiblw_qstep_diff] <- (new in this file)
   [leiblw_pof_spec] <- [leiblw_pof_spec] at [LW0LeibWindow.v:L1055-L1096]
   [leiblw_cert_core] <- [leiblw_cert_core] at [LW0LeibWindow.v:L1099-L1103]
   [leiblw_cert] <- [leiblw_cert] at [LW0LeibWindow.v:L1105-L1135]
*)
```

## PiLeibnizCReal.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiLeibnizCReal.v] lines 991-1070.

```coq
(* Statement provenance: for every statement of this file, the
   source statement of this development that it was migrated from,
   with the source coordinates.  Rows marked (new) are statements
   first stated in this file.

   [lp_a] <- [lp_a] at [S10_KVQuantTrig.v:L2693]
   [lp_pair] <- [lp_pair] at [S10_KVQuantTrig.v:L2695]
   [lp_odd] <- [lp_odd] at [S10_KVQuantTrig.v:L2697]
   [lp_four] <- [lp_four] at [S10_KVQuantTrig.v:L2703]
   [lw0m_xL] <- [lw0m_xL] at [LW0MLicBridge.v:L20]
   [piL_lp_a_0] <- (new in this file)
   [piL_lp_a_S] <- (new in this file)
   [znat_le_mono] <- (new in this file)
   [znat_eq_inj] <- (new in this file)
   [piL_pos_succ1] <- (new in this file)
   [piL_nat_pow2_ge1] <- (new in this file)
   [piL_qpow2_neq0] <- (new in this file)
   [piL_qpow2_neg] <- (new in this file)
   [qle_minus0] <- (new in this file)
   [qle0_minus] <- (new in this file)
   [qle_minus_compat] <- (new in this file)
   [qle_rsub_antitone] <- (new in this file)
   [qle_minus_flip0] <- (new in this file)
   [piL_qabs_le_nonneg] <- (new in this file)
   [piL_qabs_neg_le] <- (new in this file)
   [piL_qabs_sym] <- (new in this file)
   [piL_nat_lt_succ_le] <- (new in this file)
   [piL_even_le] <- (new in this file)
   [piL_even_le_odd] <- (new in this file)
   [piL_odd_le_even] <- (new in this file)
   [piL_odd_le_odd] <- (new in this file)
   [piL_sandwich_abs] <- (new in this file)
   [piL_sandwich_abs_neg] <- (new in this file)
   [piL_qmult_make4] <- (new in this file)
   [piL_qopp_make] <- (new in this file)
   [piL_pair_val] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_qlt_transport] <- (new in this file)
   [piL_zlt_add5] <- (new in this file)
   [piL_qclose_exp] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_depth] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_depth_pos] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_depth_floor] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_step_diff] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_t_shift] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [leiblw_xL_eq_S] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_tail_even_abs] <- (new in this file)
   [piL_tail_odd_abs] <- (new in this file)
   [piL_tail_ee] <- (new in this file)
   [piL_tail_eo] <- (new in this file)
   [piL_tail_oe] <- (new in this file)
   [piL_tail_oo] <- (new in this file)
   [leiblw_S_tail_bound] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_seq_pair_bound] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_seq] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_seq_negtail] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_t_2p2_even] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_t_even_antitone] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_tail2_antitone] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_tail2_qclose] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_qpow2_ge1] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_cauchy_neg] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_cauchy_pos] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_cauchy] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_negtail_cauchy] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_scale] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz_bound] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [pi_leibniz] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [lw0m_e] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [nivwin_pos] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [nivwin_antitone] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_inject_add1] <- (new in this file)
   [piL_e_split2] <- (new in this file)
   [piL_qinv_inject_succ] <- (new in this file)
   [lw0m_modulus] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [piL_qmult_cancel] <- (new in this file)
   [piL_e_split1] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [lw0m_modulus_bound] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [leiblw_lic_vanish] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
   [lw0m_vanish_pi] <- (new in this file; design ancestry: [maps/modulus-conversion-design.md], Section 3)
*)
```

## PiSeparation.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiSeparation.v] lines 361-392.

```coq
(* Statement provenance: for every statement of this file, the
   source statement of this development that it was migrated from,
   with the source coordinates.  Rows marked (new) are statements
   first stated in this file.

   [pi_sep_qltT_down] <- (new in this file; the down-level bridge of
      the decision wrappers, restated with the [Qcompare] three-way
      split proof body of [PiCompareT.v])
   [pi_sep_qltT_up_wc] <- (new in this file; the cross-family bridge
      into the unified-window consumption face)
   [pi_sep_pow2_witness] <- (new in this file)
   [pi_sep_n0_select] <- (new in this file; the unified two-threshold
      depth selection of [leibsep_pi_rational_unconditional] at
      [LW0LeibSeparation.v:L5697-L5719], split into the pair
      ([n0], [2^n0]))
   [pi_sep_escape_conj] <- [leibsep_pi_rational_unconditional] (the
      two branches of the guarded application) at
      [LW0LeibSeparation.v:L5716-L5718]
   [pi_sep_coupling] <- (new in this file; the upstream coupling leg
      carries no existing proof)
   [creal_escape_window_pi_leibniz] <- [creal_escape_window]
      (statement face) at [ConstructiveCauchyRealsSep.v:L99]; the
      confluence of the four assembly steps of
      [leibsep_pi_rational_unconditional] at
      [LW0LeibSeparation.v:L5697-L5719]
   [pi_leibniz_appart_all_Q] <- [creal_escape_window_apart] (the
      final jump taken directly) at [ConstructiveCauchyRealsSep.v:L108]
   [pi_leibniz_strong_irrational] <-
      [leibsep_pi_rational_unconditional] (the unconditional
      separation, restated in the [a/b] form) at
      [LW0LeibSeparation.v:L5697-L5719]
*)
```

## PiCompareT.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiCompareT.v] lines 176-201.

```coq
(* Statement provenance: for every statement of this file, the
   source statement of this development that it was migrated from,
   with the source coordinates.  Rows marked (new) are statements
   first stated in this file.

   [Id] <- [Id] at [S01_BaseRing.v:L41-L43]
   [id_trans] <- [id_trans] at [S01_BaseRing.v:L59-L62]
   [Qlt_bool] <- [Qlt_bool] at [S02_CauchyComplete.v:L42-L47]
   [QltT] <- [QltT] at [S02_CauchyComplete.v:L48]
   [QleT'] <- [QleT'] at [S02_CauchyComplete.v:L99]
   [qltw_S02_Qlt_bool] <- [Qlt_bool] (restated as [qltw_S02_Qlt_bool]) at [S02_CauchyComplete.v:L42-L47]
   [qltw_S02_Qle_bool] <- [Qle_bool] (restated as [qltw_S02_Qle_bool]) at [S02_CauchyComplete.v:L92-L96]
   [qltw_Qlt_bool_Qcompare] <- (new in this file)
   [qltw_Qle_bool_Qcompare] <- (new in this file)
   [qltw_Qeq_bool_Qcompare] <- (new in this file)
   [qltw_Qlt_bool_orig] <- (new in this file)
   [qltw_Qle_bool_orig] <- (new in this file)
   [qltw_QltT_orig] <- (new in this file)
   [qltw_S02_QltT] <- (new in this file)
   [qltw_QleT'_orig] <- (new in this file)
   [qltw_S02_QleT'] <- (new in this file)
   [qltw_samp_QltT_0_1] <- (new in this file)
   [qltw_samp_QleT'_1_1] <- (new in this file)
   [qltw_samp_Qeq_bool_2_2] <- (new in this file)
*)

```

## PiCRealAppartT.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiCRealAppartT.v] lines 131-144.

```coq
(* Statement provenance: for every statement of this file, the source
   statement that it mirrors, with the source coordinates.  Rows
   marked (new) are statements first stated in this file.

   [CRealLtT] <- [CRealLt] at [ConstructiveCauchyReals] (stdlib, the
      mirrored original; the predicate component replaced by [QltT])
   [CReal_appartT] <- [CReal_appart] at [ConstructiveCauchyReals]
      (stdlib, the mirrored original)
   [CRealLtT_of_CRealLt] <- (new in this file)
   [CRealLt_of_CRealLtT] <- (new in this file)
   [creal_appartT_of_appart] <- (new in this file)
   [creal_appart_of_appartT] <- (new in this file)
   [creal_appartT_half_third] <- (new in this file)
*)
```

## PiSep361RefaceT.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiSep361RefaceT.v] lines 92-104.

```coq
(* Statement provenance: for every statement of this file, the source
   statement that it mirrors or registers, with the source
   coordinates.  Rows marked (new) are statements first stated in
   this file.

   [leibniz_qeq_transport_blocked] <- (new in this file;
      machine-checks the premise-face note recorded at
      [PiSepBNeq0T.v] and fixes the audited premise slot
      [PiSeparation.v:L361-L362] to its honest re-facing)
   [qeq_face_to_leibniz_face] <- composition of [Qneq0T_qeq_up] and
      [Qneq0T_down] at [PiSepBNeq0T.v] (the registered one-way
      chain, stated here for reference)
*)
```

## PiSepBNeq0T.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiSepBNeq0T.v] lines 116-127.

```coq
(* Statement provenance: for every statement of this file, the source
   statement that it mirrors or re-faces, with the source coordinates.
   Rows marked (new) are statements first stated in this file.

   [Qneq0T] <- the premise face [b <> 0] of
      [pi_leibniz_strong_irrational] at [PiSeparation.v:L361-L362]
      (re-faced to the Set-carried sum form)
   [Qneq0T_down] <- (new in this file)
   [Qneq0T_qeq_down] <- (new in this file)
   [Qneq0T_qeq_up] <- (new in this file)
   [qneq0T_two] <- (new in this file)
*)
```

## PiSepTriple227.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiSepTriple227.v] lines 84-99.

```coq
(* Statement provenance: for every statement of this file, the source
   statement that it mirrors, with the source coordinates.  Rows
   marked (new) are statements first stated in this file.

   [window_family_e0] <- the documented sample point
      [e 0 = 5 # 2] at [README.md] (Guarantees)
   [window_family_e1] <- the documented sample point
      [e 1 = 5 # 4] at [README.md] (Guarantees)
   [window_family_e2] <- the documented sample point
      [e 2 = 5 # 6] at [README.md] (Guarantees)
   [triple_margin_5_8] <- the escape-witness triple
      [(22 # 7, 5 # 8, 3%nat)] at [README.md] (Guarantees; the
      margin component, cross-checked against [lw0m_e 3])
   [triple_q_227_check] <- the escape-witness triple at [README.md]
      (the [q] component, the sample point itself)
*)
```

## PiSepMirrorT.v statement-provenance ledger

Migrated from [theories/Reals/Cauchy/PiSepMirrorT.v] lines 113-123.

```coq
(* Statement provenance: for every statement of this file, the source
   statement that it mirrors, with the source coordinates.  Rows
   marked (new) are statements first stated in this file.

   [pi_leibniz_appart_all_Q_T] <-
      [pi_leibniz_appart_all_Q] at [PiSeparation.v:L349-L350]
   [pi_leibniz_strong_irrational_T] <-
      [pi_leibniz_strong_irrational] at [PiSeparation.v:L361-L362]
   [pi_leibniz_strong_irrational_T_qeq] <- (new in this file)
   [creal_appartT_pi_227] <- (new in this file)
*)
```

## PiKernelSlack.v header merged-segment ledger

Migrated from [theories/Reals/Cauchy/PiKernelSlack.v] lines 71-102.

```coq
(*
   Merged-segment mission ledger (the source file name and digest of each
   segment are recorded in the separator note line at the head of that
   segment):
   Segment 1, the identity bundle -- the stratification of the partial
   sums of the sin/cos double-angle identities and the Pythagorean
   identity (with explicit truncation residual terms), the quadruple-angle
   composite stratification, the substitution interface at the pi_L window
   points, and the residual factor control bounds.
   Segment 2, the remainder bundle -- factor control bounds for the
   residuals of the sin/cos Taylor partial sums: term-level and
   partial-sum-level absolute value bounds, an explicit per-term majorant
   recursion for the residuals, and three master bounds.
   Segment 3, the reduction piece -- the reduction bound for the vanishing
   vertex factor: |C-S| <= |C^2-S^2| (under the premise 1 <= C+S), with a
   minimal companion interface for consuming the vertex zero anchor.
   Segment 4, the synthesis premise bundle -- an explicit pure-Q chain
   dominating power tails by factorial tails, the geometric decay of the
   Taylor terms, tail sums dominated by the first omitted term, the
   half-power witness, the uniform Cauchy face of the partial sums, and
   the Cauchy face of the double-angle residual majorant series.
   Segment 5, the two-index synthesis bundle -- the two-index vanishing
   synthesis of the sin/cos partial sums at the window points (three
   explicit seed slots carried at the Set level, plus the identity
   gathering and order bookkeeping auxiliaries).
   Segment 6, the separation kernel -- the Leibniz series separation
   kernel [leibsep_q_kernel]: for every rational q it provides a positive
   distance witness c and a threshold N such that every sample point
   [lw0m_xL m] beyond N stays at distance more than c from q; the proof
   chain runs: the two triangular-window vanishing pieces (carried by the
   three seed premises) -> the tail rescaling [caps_scaled] -> the margin
   assembly. *)
```

## PiVertexPolyDiff.v source-region register

Each derivation comment of [theories/Reals/Cauchy/PiVertexPolyDiff.v]
carried a source-region coordinate of the internal development files
[S03_QExp.v] / [S10_KVQuantTrig.v] (not part of this package).  The
coordinates are registered here (frozen as recorded; line numbers refer
to PiVertexPolyDiff.v at package state 52d41fa, before the comments were
rewritten to name-level citations).

| PiVertexPolyDiff.v line | source coordinate |
|---|---|
| 35 | S03_QExp.v@2516 |
| 61 | S03_QExp.v@2516 |
| 92 | S03_QExp.v@3576 |
| 152 | S10_KVQuantTrig.v@6418 |
| 163 | S03_QExp.v@4210 |
| 173 | S03_QExp.v@4217 |
| 183 | S10_KVQuantTrig.v@6726 |
| 196 | S10_KVQuantTrig.v@6769 |
| 236 | S10_KVQuantTrig.v@6805 |
| 241 | S10_KVQuantTrig.v@6809 |
| 250 | S10_KVQuantTrig.v@7218 |
| 259 | S10_KVQuantTrig.v@7226 |
| 271 | S10_KVQuantTrig.v@6872 |
| 295 | S10_KVQuantTrig.v@6850 |
| 314 | S10_KVQuantTrig.v@6895 |
| 327 | S10_KVQuantTrig.v@6905 |
| 374 | S10_KVQuantTrig.v@6942 |
| 390 | S10_KVQuantTrig.v@6956 |
| 438 | S10_KVQuantTrig.v@7082 |
| 463 | S10_KVQuantTrig.v@7105 |
| 481 | S10_KVQuantTrig.v@7131 |
| 485 | S10_KVQuantTrig.v@7117 |
| 497 | S10_KVQuantTrig.v@7129 |
| 514 | S10_KVQuantTrig.v@7151 |
| 543 | S10_KVQuantTrig.v@7193 |
| 561 | S10_KVQuantTrig.v@7211 |
| 590 | S10_KVQuantTrig.v@7234 |
| 620 | S10_KVQuantTrig.v@7246 |
| 640 | S10_KVQuantTrig.v@7268 |
| 669 | S10_KVQuantTrig.v@7296 |
| 683 | S10_KVQuantTrig.v@7310 |
| 696 | S10_KVQuantTrig.v@5232 |
| 707 | S10_KVQuantTrig.v@7324 |
| 741 | S10_KVQuantTrig.v@7290 |
| 760 | S10_KVQuantTrig.v@7316 |

