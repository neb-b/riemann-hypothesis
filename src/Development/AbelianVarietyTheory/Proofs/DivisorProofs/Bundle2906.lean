module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DivDeep

theorem root_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {z : M.Z}
    (hn : IsIntegrallyClosed (M.O z)) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : u ∈ M.O z := by
  have hint : IsIntegral (M.O z) u := ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

theorem exists_eq_smul_of_smul_eq_zero {L k : ℕ} (hL : 0 < L) (hk : k ∣ L) (a : ZMod L) (ha : k • a = 0) :
    ∃ x : ZMod L, (L / k) • x = a := by
  obtain ⟨d, rfl⟩ := hk
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hL)
  haveI : NeZero (k * d) := ⟨hL.ne'⟩
  rw [Nat.mul_div_cancel_left _ hk]
  have h : ((k * a.val : ℕ) : ZMod (k * d)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, ha]
  obtain ⟨e, he⟩ := Nat.dvd_of_mul_dvd_mul_left hk ((ZMod.natCast_eq_zero_iff _ _).1 h)
  exact ⟨e, by rw [nsmul_eq_mul, ← Nat.cast_mul, ← he, ZMod.natCast_zmod_val]⟩

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem exists_div_of_isLab (X : Setup F W i) {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (c : CTrait X p z) {yy}
    (h : IsLab X ε c yy) {k : ℕ} (hk : 2 ≤ k) (hd : k ∣ X.S.r * X.S.N) :
    ∃ a : X.S.Gam, k • a = 0 ∧ X.M.Div X.S.th a z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hle, y₀, hy₀, u, l, j, hq, -⟩ := h
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one c.cen ((X.M.O z).algebraMap_mem a)
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    refine hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg ?_ (by positivity)))))
    rw [hq]
    exact mul_nonneg c.scale_pos.le (by
      exact_mod_cast qW_nonneg_of_posW W X.posW c.T.β c.T.symm (Basic₂.trait_nonneg c.T) (j w))
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, ?_⟩
  obtain ⟨d, hdv⟩ := X.div z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff c.cen (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes c.cen
  have e : ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ =
      ‖y₀ ⟨c₀ * X.S.th d, hth d⟩‖ * ‖X.M.val (gPt p ≫ c.y) (X.S.th a / X.S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul (z := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)))
      (fun w => by rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]) (hle (hth d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have hn' : ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ = sc := hn
  have b₁ := RatModel.norm_val_le_one c.cen (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (X.M.val (gPt p ≫ c.y) (X.S.th a / X.S.th d)))
  nlinarith

theorem exists_div_torsion (X : Setup F W i) {ε} (hε : IsDiagEnd F W X.ρ.P X.u ε) (z : X.M.Z) {k : ℕ} (hk : 2 ≤ k)
    (hd : k ∣ X.S.r * X.S.N) : ∃ a : X.S.Gam, k • a = 0 ∧ X.M.Div X.S.th a z := by
  haveI := X.M.qc
  haveI := X.imm
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z', hz', hcl⟩ := (isClosed_closure (s := {z})).exists_closed_singleton ⟨z, subset_closure rfl⟩
  have hsp : z ⤳ z' := specializes_iff_mem_closure.2 hz'
  obtain ⟨p, _, y, hy, hU⟩ := exists_cen_main _ _ X.M z' hcl (X.π ⁻¹ᵁ i.opensRange)
    ⟨X.M.pt (closedPoint X.Ω₁), by
      show (X.M.pt ≫ X.π) _ ∈ Set.range i
      rw [X.comp]
      exact ⟨_, rfl⟩⟩
  obtain ⟨c, -⟩ := GCTrait.exists_cTrait g n F W Z i X X.one_le X.three_le X.odd X.imm p y (by
    rintro _ ⟨w, rfl⟩
    exact hU ⟨w, rfl⟩)
  obtain ⟨yy, hyy⟩ := exists_isLab g n F W Z i X X.one_le X.three_le X.odd X.imm X.e8 X.thetaInt X.projM ε hε p _ c
  obtain ⟨a, ha, hdv⟩ := exists_div_of_isLab X c hyy hk hd
  exact ⟨a, ha, hdv.of_specializes (hy ▸ hsp)⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (z₁ : X₁.M.Z) (x₀ : X₁.S.Gam), x₀ ∈ X₁.S.supI X₁.M z₁ → ∀ (z' : D.X.M.Z), D.q z' = z₁ → D.X.M.Div D.X.S.th (D.lab x₀) z' := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D z₁ x₀ hx₀ z' hz'
  have hx : X₁.M.Div X₁.S.th x₀ z₁ := hx₀
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N :=
    (D.dvd.trans (D.sq ▸ dvd_pow_self D.m two_ne_zero)).trans (dvd_mul_left _ _)
  obtain ⟨a, ha, hdv⟩ := exists_div_torsion D.X D.diag z'
    (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < D.X.S.r * D.X.S.N := Nat.mul_pos D.X.S.r_pos (by have := D.X.S.N_ge; omega)
  choose x hxa using fun s => exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  obtain ⟨b, hb⟩ := D.lab_range x
  obtain rfl : D.lab b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := same_ratio D.same x₀ b
  set φ := algebraMap X₁.Ω₁ D.X.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : D.X.S.th (D.lab x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (D.X.M.O z') := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := D.X.normal
    exact ⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z'
  have m₁ : D.X.S.th (D.lab b) * φ (X₁.S.th x₀) / (D.X.S.th (D.lab x₀) * φ (X₁.S.th b)) ∈ D.X.M.O z' :=
    root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ D.X.M.O z' := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨D.q ⁻¹ᵁ U, D.q.app U f, show D.q z' ∈ U from hz' ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp D.X.M.pt D.q U f).symm.trans ?_
    rw [D.gen, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp

end GlobalTheory.Poinc.DivDeep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupLabellingTransportGaloisConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GalTrans

section Cong
variable {X : Type} [AddCommGroup X]

theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨-w, by rw [hw, smul_neg]; abel⟩

theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  exact ⟨w' + w, by rw [hw, hw', smul_add]; abel⟩

theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, by rw [hw, map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.mp h
  change N • w = -x + y at hw
  refine ⟨-w, ?_⟩
  rw [smul_neg, hw]
  abel

theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  obtain ⟨w, hw⟩ := h
  refine QuotientAddGroup.eq.mpr ⟨-w, ?_⟩
  change N • (-w) = -x + y
  rw [hw, smul_neg]
  abel
private theorem charZero_uTest_V {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) : CharZero u.V :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong


open MonObj in
theorem compare {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} {y₁ : S'.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (l : u.Lab)
    (l' : u'.Lab) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left)
    (ha : IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a)
    (ha' : IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a')
    (hL : LBIso P₀.L (u.A.L.pull a)) (hL' : LBIso P₀.L (u'.A.L.pull a')) :
    ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ, l'.q (e χ) = l.q χ) ∧
      (∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A)
        (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → x ^ m = 1 → x' ^ m = 1 → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left →
        w ≫ a' = x'.left → ∃ pk pk', QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧
          QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' ∧ CongMod m pk'.y (e pk.y)) ∧
      ∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), 1 ≤ m →
        QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) m)
          (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left),
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧ x ^ m = 1 ∧ w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧
          w ≫ a' = x'.left ∧ CongMod m pk'.y (e pk.y) := by
  obtain ⟨e, hps, hcg⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations S S' ρ ρ' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI := charZero_uTest_V u
  haveI := charZero_uTest_V u'
  refine ⟨e, fun χ => ?_, fun m x x' w hm hx hx' hw hwa hwa' => ?_, fun m pk' x' hm hpk' => ?_⟩
  · have h1 := (hps χ _).1 (l.q_eq χ)
    have h2 := l'.q_eq (e χ)
    have h3 := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 h1)
    linarith
  · obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨f', hf1', hf2', -⟩ := GlobalTheory.ZH.uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    obtain ⟨pk', rfl⟩ := hf2' x' hx'
    have q1 := (hf1 pk (f pk)).2 rfl
    have q2 := (hf1' pk' (f' pk')).2 rfl
    exact ⟨pk, pk', q1, q2, hcg m pk pk' _ _ w hm q1 q2 hw hwa hwa'⟩
  · have hx' : x' ^ m = 1 := by
      have h0 := hpk'
      unfold QkToAkU at h0
      obtain ⟨w0, hw0⟩ := u'.U.ext
      have h1 := h0 w0 hw0
      unfold QkToAk at h1
      exact h1.1
    obtain ⟨w, x, hw, hwa', hwa, hx⟩ :=
      GlobalTheory.PtTrans.ptTrans (PadicAlgCl p) u'.A u.A P₀ a' a ha' ha m x' hx'
    obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    have q1 := (hf1 pk (f pk)).2 rfl
    exact ⟨pk, f pk, w, q1, hx, hw, hwa, hwa', hcg m pk pk' _ _ w hm q1 hpk' hw hwa hwa'⟩

set_option maxHeartbeats 1000000 in
theorem isLab_conj : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∀ (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro g n F W Z i X₁ hg hn hodd hi hE8 hth hpr ε₁ hdiag D σ s hs a hga p _ z₁ c y h h' yy hlab
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame', hi₀', hR', y₀, hy₀, u, l, j, hq, hlabl, hmat⟩ := hlab
  obtain ⟨yy₂, hlab₂⟩ := exists_isLab g n F W Z i D.X hg hn hodd hi hE8 hth D.proj D.ε D.diag p
    ((y ≫ s) (cPt p)) (D.lift c (y ≫ s) h')
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, j₂, hq₂, -, -⟩ := hlab₂
  obtain ⟨P₀, b, t, ε₀, hb, ht, lb, lt, hε, hp⟩ := hga
  obtain ⟨Q, b', b'', hb', hb'', lb', lb'', hpts, hend⟩ :=
    exists_generic D.X.ρ D.ε ρ' ε' ρ₂ ε₂ (fun x => x) (fun x => x) hsame' hsame₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) a P₀ b t ε₀
      hb ht lb lt hε hp
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  have hR₂' : R₂ ≤ D.X.M.O (((gPt p ≫ y) ≫ s) (closedPoint (PadicAlgCl p))) := by
    rw [Category.assoc]; exact hR₂
  have hy₁' : ∀ r : R₂, y₁ r = D.X.M.val ((gPt p ≫ y) ≫ s) r := by
    intro r; rw [Category.assoc]; exact hy₁ r
  have hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := by
    have hn := D.X.normal
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme
    obtain ⟨h1, h2⟩ := hn
    exact fun x => ⟨h1 x, h2 x⟩
  obtain ⟨P₁, a₁, a₂, ha₁, ha₂, la₁, la₂, hpt, hen⟩ :=
    spread D.X.M hM ρ' ρ₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs (gPt p ≫ y) hR' hR₂' y₀ y₁ hy₀ hy₁' u u₂ Q hb' hb''
      lb' lb''
  obtain ⟨e, heq, hfw, hbk⟩ := compare u u₂ l l₂ P₁ a₁ a₂ ha₁ ha₂ la₁ la₂
  have hN : 1 ≤ D.X.S.r * D.X.S.N := by
    obtain ⟨jj, -, hr⟩ := D.X.ρ.r_eq
    rw [hr, D.X.ρ.N_eq]
    have hnp := D.X.ρ.n_prime.pos
    exact Nat.mul_pos (pow_pos hnp _) (pow_pos (pow_pos hnp _) _)
  refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, e.symm.trans j, ?_, ?_, ?_⟩
  · intro χ
    have h1 := heq (e.symm χ)
    rw [AddEquiv.apply_symm_apply] at h1
    rw [h1]
    exact hq (e.symm χ)
  · intro bb χ hb2
    obtain ⟨wg, hwg, hwg1, hwg2⟩ := hpts bb
    obtain ⟨w1, x1, x2, hw1, hw1a, hw1b, hx1, hx2⟩ := hpt (a bb) bb wg hwg hwg1 hwg2
    have hx1p := GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u (a bb) x1 hx1
    have hx2p := GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ₂ p y₁ u₂ bb x2 hx2
    obtain ⟨pk, pk2, hq1, hq2, hc12⟩ := hfw (D.X.S.r * D.X.S.N) x1 x2 w1 hN hx1p hx2p hw1 hw1a hw1b
    have e1 := l.yy_eq (a bb) pk x1 hq1 hx1
    have e2 := l₂.yy_eq bb pk2 x2 hq2 hx2
    have c1 : CongMod (D.X.S.r * D.X.S.N) χ pk2.y := cm_of_mk (hb2.symm.trans e2)
    have c2 := cm_trans c1 hc12
    have c3 : CongMod (D.X.S.r * D.X.S.N) (e.symm χ) pk.y := by
      have c4 := cm_map e.symm.toAddMonoidHom c2
      simpa using c4
    have e3 : l.yy (a bb) = QuotientAddGroup.mk (e.symm χ) := e1.trans (cm_mk (cm_symm c3))
    exact hlabl (a bb) (e.symm χ) e3
  · intro m pk pk' x x' E hm hq hq' hxx
    obtain ⟨pk0, x0, w0, hq0, hx0, hw0, hw0a, hw0b, hc0⟩ := hbk m pk x hm hq
    obtain ⟨pk0', x0', w0', hq0', hx0', hw0', hw0a', hw0b', hc0'⟩ := hbk m pk' x' hm hq'
    obtain ⟨η, hη1, hη2⟩ := hend E
    have hyp : w0' ≫ a₂ ≫ u₂.φ = w0 ≫ a₂ ≫ u₂.φ ≫ (ε₂ E).left := by
      rw [← hw0b', ← hw0b] at hxx
      simpa only [Category.assoc] using hxx
    have key : x0'.left ≫ u.φ = x0.left ≫ u.φ ≫ (ε' E).left := by
      have k1 := hen (ε' E) (ε₂ E) η hη1 hη2 w0 w0' hw0 hw0' hyp
      rw [← hw0a', ← hw0a]
      simpa only [Category.assoc] using k1
    have hm0 := hmat m pk0 pk0' x0 x0' E hm hq0 hq0' key
    have A : CongMod m (j (e.symm pk'.y)) (j pk0'.y) := by
      have A1 := cm_map (e.symm.trans j).toAddMonoidHom hc0'
      simpa using A1
    have B : CongMod m (j (e.symm pk.y)) (j pk0.y) := by
      have B1 := cm_map (e.symm.trans j).toAddMonoidHom hc0
      simpa using B1
    have B2 := cm_map (matAct E) B
    exact cm_trans A (cm_trans hm0 (cm_symm B2))

end GlobalTheory.Poinc.GalTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenPtOpen

theorem top_le_preimage_of_valR_injective : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ O : P₀.A.left.Opens, (O : Set P₀.A.left).Nonempty → ⊤ ≤ ξ ⁻¹ᵁ O := by
  intro K _ P₀ F _ ψ ξ _ H O hO
  haveI : IsIntegral P₀.A.left := GlobalTheory.isIntegral_left_of_isAbelianScheme_field P₀.A P₀.isAb
  by_contra hno
  haveI : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have key : ∀ V : P₀.A.left.Opens, ξ p ∈ V → ⊤ ≤ ξ ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y p]; exact hV
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    P₀.A.left.isBasis_affineOpens) (show ξ p ∈ (⊤ : P₀.A.left.Opens) from trivial)
  obtain ⟨y, hyU, hyO⟩ := nonempty_preirreducible_inter U.isOpen O.isOpen ⟨_, hxU⟩ hO
  obtain ⟨f, hfO, hyf⟩ := (show IsAffineOpen U from hU).exists_basicOpen_le (V := O) ⟨y, hyO⟩ hyU
  have hUt : ⊤ ≤ ξ ⁻¹ᵁ U := key U hxU
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  refine hf0 (H U f hUt ?_)
  by_contra hv
  have hu : IsUnit (valR ξ U f) := isUnit_iff_ne_zero.mpr hv
  have hb := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff ξ U hUt f).mp hu
  exact hno (hb.trans (ξ.preimage_mono hfO))

end GlobalTheory.GenPtOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMa
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocReg

theorem comp_genι_eq_spMap_chartHom (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) :
    ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  have hx' : (ξ ≫ genι Y) (closedPoint (ChartRing k m d)) ∈ U.1 := hx
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (ξ ≫ genι Y)
  have e2 : Y.X.fromSpecStalk ((ξ ≫ genι Y) (closedPoint (ChartRing k m d))) =
      Spec.map (Y.X.presheaf.germ U.1 _ hx') ≫ U.2.fromSpec :=
    (U.2.fromSpecStalk_eq_fromSpecStalk hx').symm
  rw [e2, ← Spec.map_comp_assoc, Scheme.stalkClosedPointTo_comp] at e1
  rw [← e1, chart]
  congr 2
  exact (Scheme.Hom.germ_stalkMap_assoc (genι Y) U.1 (ξ (closedPoint _)) hx (Scheme.stalkClosedPointTo ξ)).trans rfl

end GlobalTheory.LocReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartRingMapFlatAndComapMaximalIdeal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.LocRegFlat

theorem germ_flat {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.Flat := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)

theorem chartHom_flat_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ mm : Ideal Γ(Y.X, U.1), mm.IsMaximal → (∀ f ∈ mm, genι Y (ξ (closedPoint _)) ∉ Y.X.basicOpen f) → (GlobalTheory.LocReg.chartHom Y U ξ hx).Flat ∧ (maximalIdeal (ChartRing k m d)).comap (GlobalTheory.LocReg.chartHom Y U ξ hx) = mm := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx he mm hmm hmem
  have key : GlobalTheory.LocReg.chartHom Y U ξ hx = ((Y.X.presheaf.germ U.1 (genι Y (ξ (closedPoint _))) hx ≫
      (genι Y).stalkMap (ξ (closedPoint _))) ≫ Scheme.stalkClosedPointTo ξ).hom := by
    have h := (genι Y).germ_stalkMap U.1 (ξ (closedPoint _)) hx
    unfold GlobalTheory.LocReg.chartHom
    rw [h]; rfl
  rw [key]
  simp only [CommRingCat.hom_comp]
  have hg := germ_flat U.2 _ hx
  have hs : ((genι Y).stalkMap (ξ (closedPoint _))).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  refine ⟨(hg.comp hs).comp he.1, ?_⟩
  symm
  refine hmm.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top) ?_
  intro f hf
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hmem f hf
  rw [Scheme.mem_basicOpen]
  simp only [RingHom.comp_apply] at hu
  exact isUnit_of_map_unit ((genι Y).stalkMap _).hom _ (isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom _ hu)
  exact hx
end GlobalTheory.LocRegFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ∀ a, b a = v' a := by
  first | exact @GlobalTheory.TanRay.tanBasis_of_isPointOf | exact GlobalTheory.TanRay.tanBasis_of_isPointOf | (intros; apply GlobalTheory.TanRay.tanBasis_of_isPointOf <;> assumption)
end

