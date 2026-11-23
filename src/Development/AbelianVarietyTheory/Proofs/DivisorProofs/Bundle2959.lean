module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffWeilIsAbelianPart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0023
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0029
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatum
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.GradedTate

theorem exists_tateIso_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H)
    (Z : Submodule (𝓞 E) Dw.La) (f : perp Dw Z →ₗ[𝓞 E] D'.La) (hf : IsLower Dw D' Z f) (K : Type) [Field K]
    (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (ζ : ℕ → Kˣ)
    (hζ : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hζ' : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (b : ℕ → perp Dw Z → Q) (hact : ∀ c, act c 1 = 1)
    (hcard : ∀ n, 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D'.La)
    (huniq : ∀ n x y c c', e n x y c → e n x y c' → c = c')
    (hone : ∀ n y c, e n 1 y c → c = 1)
    (hadd : ∀ n, 0 < n → ∀ a a', b n (a + a') = b n a * b n a')
    (hlin : ∀ n, 0 < n → ∀ (c : 𝓞 E) a, b n (c • a) = act c (b n a))
    (hpow : ∀ n, 0 < n → ∀ a, b n a ^ n = 1)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, b (n * m) a ^ m = b n a)
    (hiso : ∀ n, 0 < n → ∀ a a', e n (b n a) (b n a') (ζ n ^ Dw.EF a a')) :
    ∃ I' : TateIso D' K Q act e, (∀ n, I'.ζ n = ζ n) ∧ ∀ n, 0 < n → ∀ a, b n a = I'.ev n (f a) := by
  have := D'.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf.1
  have hs' : ∀ w, f (s w) = w := fun w => LinearMap.congr_fun hs w
  have hiso' : ∀ n, 0 < n → ∀ a w', e n (b n a) (b n (s w')) (ζ n ^ D'.EF (f a) w') := fun n hn a w' => by
    have h := hiso n hn a (s w')
    rwa [← hf.2.2, hs'] at h
  have hiso'' : ∀ n, 0 < n → ∀ w w', e n (b n (s w)) (b n (s w')) (ζ n ^ D'.EF w w') := fun n hn w w' => by
    have h := hiso' n hn (s w) w'
    rwa [hs'] at h
  have hadd' : ∀ n, 0 < n → ∀ w w', b n (s (w + w')) = b n (s w) * b n (s w') := fun n hn w w' => by
    rw [map_add (f := _), hadd n hn]
  have hko := fun n (hn : 0 < n) => TorsIsometry.ker_and_onto E H D' K Q (e n) n (ζ n) (fun w => b n (s w)) hn
    (hcard n hn) (fun y c _ => hone n y c) (hζ n hn) (hadd' n hn) (fun w => hpow n hn _) (hiso'' n hn)
  refine ⟨{ ζ := ζ, ζ_prim := hζ, ζ_pow := hζ', ev := fun n w => if 0 < n then b n (s w) else 1
            add := fun n w w' => ?_, lin := fun n c w => ?_, ker := fun n hn => ?_, onto := fun n hn => ?_
            tower := fun n m hn hm w => ?_, isom := fun n hn w w' => ?_ }, fun _ => rfl, fun n hn a => ?_⟩
  · split_ifs with hn
    · exact hadd' n hn w w'
    · exact (_root_.mul_one _).symm
  · split_ifs with hn
    · rw [map_smul, hlin n hn]
    · exact (hact c).symm
  · simp only [if_pos hn]
    exact (hko n hn).1
  · simp only [if_pos hn]
    exact (hko n hn).2
  · simp only [if_pos hn, if_pos (Nat.mul_pos hn hm)]
    exact htow n m hn hm _
  · simp only [if_pos hn]
    exact hiso'' n hn w w'
  · show _ = if 0 < n then b n (s (f a)) else 1
    rw [if_pos hn]
    obtain ⟨w, hw⟩ := ((hko n hn).2 _).1 (hpow n hn a)
    obtain ⟨c, hc⟩ := TorsIsometry.exists_eq_nsmul_of_dvd D'.EF D'.unimod n (f a - w) fun w' => by
      have h₁ := hiso' n hn a w'
      rw [← hw] at h₁
      have h₂ := huniq _ _ _ _ _ h₁ (hiso'' n hn w w')
      rw [map_sub, LinearMap.sub_apply, ← (hζ n hn).zpow_eq_one_iff_dvd, zpow_sub, h₂, mul_inv_cancel]
    have h₃ : b n (s (f a - w)) = 1 := ((hko n hn).1 _).2 ⟨c, hc⟩
    have h₄ := hadd' n hn (f a - w) w
    rw [sub_add_cancel, h₃, _root_.one_mul] at h₄
    exact hw.symm.trans h₄.symm

section Pairs

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] TorusExt.gtGroup

theorem eq_of_equiv (hB : D.TauBimult) {k : ℕ} (hk : 0 < k) {p q : QkPt D F k} (h : QkPt.Equiv D F p q)
    (hy : p.y = q.y) : p = q := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 h
  have hz : k • z = 0 := by
    rw [hy] at h₁
    exact left_eq_add.1 h₁
  have : z = 0 := by
    rw [← natCast_zsmul] at hz
    exact (smul_eq_zero.1 hz).resolve_left (Int.natCast_ne_zero.2 hk.ne')
  subst this
  rw [map_zero, add_zero] at h₂
  exact TorusExt.qk_ext hy h₂.symm

theorem b_pow (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) : p.g.b ^ k = 1 := by
  rw [← TorusExt.nsmul_b, TorusExt.qk_nsmul hB, hy, map_zero, TorusExt.zero_b]

theorem b_tower (hB : D.TauBimult) {n m : ℕ} (hn : 0 < n) {p p₀ : QkPt D F (n * m)} {q r r₀ : QkPt D F n}
    (hp : QkPt.Equiv D F p p₀) (hp₀ : p₀.y = 0) (hq : q.y = p.y) (hg : GtPtF.IsNsmul m p.g q.g)
    (hr : QkPt.Equiv D F q r) (hr' : QkPt.Equiv D F r r₀) (hr₀ : r₀.y = 0) : p₀.g.b ^ m = r₀.g.b := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 hp
  have h₃ : TorusExt.qkShift hB q (m • z) = r₀ := by
    refine eq_of_equiv hB hn (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB (TorusExt.equiv_qkShift hB q _))
      (TorusExt.equiv_trans hB hr hr')) ?_
    show q.y + n • m • z = r₀.y
    rw [hr₀, hq, smul_smul, ← h₁, hp₀]
  rw [← h₃, ← TorusExt.nsmul_b, h₂, nsmul_add, ← (TorusExt.isNsmul_iff_eq _ _ _).1 hg, ← map_nsmul]
  rfl

end Pairs


attribute [local instance] TorusExt.gtGroup in
theorem exists_gradedTateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  intro E _ _ _ H Dw D' Z f hf R _ _ _ hR t P F _ _ _ hrk I hI
  letI := H.starRing
  have hB := P.D.tau_bimult
  have hL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have := hR.2
  have := hR.1.1
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  choose q hq hy using hI
  have huniq : ∀ (n : ℕ) (x y : TF (R := R) F ⟶ P.D.toPre.P.A) (c c' : Fˣ),
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c) →
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c') → c = c' := fun n x y c c' =>
    weilIs_unique_fieldPoint _ _ _ P.D.toPre.P.isLB F _ n x y c c'
  obtain ⟨I', h₁, h₂⟩ := exists_tateIso_of_perp Dw D' Z f hf F (TF (R := R) F ⟶ P.D.toPre.P.A)
    (fun a g => g ≫ P.oD.onB.act a)
    (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)) I.ζ I.ζ_prim I.ζ_pow
    (fun n a => if hn : 0 < n then (q n hn a).g.b else 1)
    (fun c => by
      have := P.oD.onB.hom c
      exact MonObj.one_comp _)
    (fun n hn => by
      have : NeZero n := ⟨hn.ne'⟩
      rw [hrk]
      exact (hL.1.mulN _ P.D.toPre.P n hn).2.2.2.2 F _
        (IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)).neZero'.ne)
    huniq
    (fun n y c h => by
      have h₁ := (hL.1.weil _ P.D.toPre.P n _).2.1 _ _ _ _ _ h h
      rw [_root_.mul_one] at h₁
      have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
      exact mul_eq_left.1 (huniq n 1 y _ _ (e ▸ h₁) h))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAdd_iff hB _ _ _).1
        ((TorusExt.qkAdd_iff_of_equiv hB (hq n hn a) (hq n hn a') (I.add n hn a a')).2 (hq n hn (a + a')))
      rw [← eq_of_equiv hB hn h (by
        show (q n hn a).y + (q n hn a').y = _
        rw [hy, hy, hy, add_zero])]
      exact TorusExt.add_b _ _)
    (fun n hn c a => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAct_iff hB hG P.oD _ _ _).1
        ((TorusExt.qkAct_iff_of_equiv hB hG P.oD (hq n hn a) (I.lin n hn c a)).2 (hq n hn (c • a)))
      rw [← eq_of_equiv hB hn h (by
        show c • (q n hn a).y = _
        rw [hy, hy, smul_zero])]
      exact TorusExt.gtSmul_b hG P.oD _ _)
    (fun n hn a => by
      simp only [dif_pos hn]
      exact b_pow hB _ (hy n hn a))
    (fun n m hn hm a => by
      simp only [dif_pos hn, dif_pos (Nat.mul_pos hn hm)]
      obtain ⟨r, r₁, r₂, r₃⟩ := I.tower n m hn hm a
      exact b_tower hB hn (hq _ _ a) (hy _ _ a) r₁ r₂ r₃ (hq n hn a) (hy n hn a))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      exact (UT.WeilAbelianPart.weilQkIs_iff_weilIs_abelianPart hL R _ hR.1 P.D F n hn _ _ (hy n hn a) (hy n hn a')
        _).1 (PhiOperatorCompare.weilQkIs_of_equiv hB (hq n hn a) (hq n hn a') (I.isom n hn a a')))
  refine ⟨I', h₁, fun n hn a r hr hr₀ => ?_⟩
  rw [← h₂ n hn a, dif_pos hn, eq_of_equiv hB hn
    (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB hr) (hq n hn a)) (hr₀.trans (hy n hn a).symm)]

end GlobalTheory.LowDat.GradedTate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorPeriodDefectZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatMod

namespace GlobalTheory.HeatMod

theorem opMod {R : Type} [CommRing R] (G : Over (Sp R)) {n : ℕ} (dd : Fin n → Fld G.left)
    (Θ M : Matrix (Fin n) (Fin n) R) (u c₁ c₂ : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W))
    (k : ℕ) (O : G.left.Opens) (f : Γ(G.left, O)) :
    op G dd (Θ + M) (u - c₁) (fun O f => d O f - combF G.hom dd c₂ O f) p p' k O f =
      op G dd Θ u d p p' k O f - 2 * (k : Γ(G.left, O)) * combF G.hom dd c₂ O f - quadF G.hom dd M O f -
        2 * combF G.hom dd c₁ O f := by
  have hc : ∀ a b : R, constFn G.hom O (a + b) = constFn G.hom O a + constFn G.hom O b := fun a b => by
    simp [constFn]
  have hs : ∀ a b : R, constFn G.hom O (a - b) = constFn G.hom O a - constFn G.hom O b := fun a b => by
    simp [constFn]
  simp only [op, combF, quadF, Matrix.add_apply, Pi.sub_apply, hc, hs, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

theorem rsT_resG_constFn {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {U V : Z.Opens} (hV : V ≤ U)
    (x : R) : rsT (resG Z (le_top : U ≤ ⊤) (constFn s ⊤ x)) V = constFn s V x := by
  rw [← GlobalTheory.KS.rsT_of_le (le_top : U ≤ ⊤), GlobalTheory.KS.rsT_rsT le_top hV, GlobalTheory.KS.rsT_constFn _ le_top]

theorem defect_cancel {R X : Type} [CommRing R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R) (half : R)
    (h2 : 2 * half = 1) (hw1 : ∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) (hw2 : ∀ mu mu', w mu mu' = w mu' mu)
    (hπ' : ∀ mu mu', π' (mu + mu') = π' mu + π' mu') (hπ : ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu)
    (k : ℕ) (mu α : X) :
    0 = 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu +
      (-(2 * (k : R) * (π (α + k • mu) - half * w (α + k • mu) (α + k • mu))) - w (α + k • mu) (α + k • mu) -
        2 * π' (α + k • mu)) -
      (-(2 * (k : R) * (π α - half * w α α)) - w α α - 2 * π' α) := by
  have wsm : ∀ (m : ℕ) (x y : X), w (m • x) y = (m : R) * w x y := by
    intro m x y
    induction m with
    | zero =>
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      have := hw1 0 0 y
      simp only [add_zero] at this
      linear_combination -this
    | succ m ih => rw [succ_nsmul, hw1, ih]; push_cast; ring
  have psm : ∀ (m : ℕ) (x : X), π' (m • x) = (m : R) * π' x := by
    intro m x
    induction m with
    | zero =>
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      have := hπ' 0 0
      simp only [add_zero] at this
      linear_combination -this
    | succ m ih => rw [succ_nsmul, hπ', ih]; push_cast; ring
  have qsm : ∀ (m : ℕ) (x : X), π (m • x) = (m : R) * π x + half * ((m : R) ^ 2 - m) * w x x := by
    intro m x
    induction m with
    | zero =>
      have := hπ 0 0
      simp only [add_zero, map_zero, AddMonoidHom.zero_apply] at this
      simp only [zero_smul, Nat.cast_zero]
      linear_combination -this
    | succ m ih =>
      rw [succ_nsmul, hπ, ih, map_nsmul, nsmul_eq_mul]
      push_cast
      linear_combination (-(m : R) * w x x) * h2
  simp only [hπ, hπ', hw1, map_add (f := _), wsm, map_nsmul, psm, qsm, nsmul_eq_mul, hw2 α mu]
  linear_combination (-((k : R) ^ 2 * w mu mu + 2 * (k : R) ^ 2 * w mu α)) * h2

theorem exists_heat_defect_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h → HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → (∀ mu mu', π' (mu + mu') = π' mu + π' mu') → (∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu) → ∃ h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h' ∧ HasDefect Y h' (fun _ _ _ => 0) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h w π π' hB hD hw1 hw2 hπ' hπ
  let ℓ₁ : Dd.toPre.X →+ R := AddMonoidHom.mk' π' hπ'
  let half : R := algebraMap ℚ R (1 / 2)
  have h2 : (2 : R) * half = 1 := by
    simp only [half]
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  let ℓ₂ : Dd.toPre.X →+ R := AddMonoidHom.mk' (fun x => π x - half * w x x) (fun a b => by
    simp only [hπ, hw1, map_add (f := _)]
    rw [hw2 b a]
    linear_combination (-(w a b)) * h2)
  obtain ⟨c₁, hc₁⟩ := _root_.GlobalTheory.HeatMod.TorField.exists_isTorField R Dd O oa Y n v dd hv ℓ₁
  obtain ⟨c₂, hc₂⟩ := _root_.GlobalTheory.HeatMod.TorField.exists_isTorField R Dd O oa Y n v dd hv ℓ₂
  obtain ⟨M, hMs, hMa, hMg⟩ := _root_.GlobalTheory.HeatMod.TorTensor.exists_quad R Dd O oa Y n v dd hv w hw1 hw2
  obtain ⟨⟨a1, a2, a3⟩, kc, wt₂, pb₂⟩ := hc₂
  let h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D :=
    { Θ := h.Θ + M
      symm := by rw [Matrix.transpose_add, h.symm, hMs]
      u := h.u - c₁
      J := h.J
      W := h.W
      j := h.j
      d := fun i O f => h.d i O f - combF Y.H.hom dd c₂ O f
      p := h.p
      p' := h.p'
      cover := h.cover
      le := h.le
      lift := fun i => by
        obtain ⟨⟨f1, f2, f3⟩, fc⟩ := h.lift i
        refine ⟨⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' hh hW f => ?_⟩, fun W hW r => ?_⟩
        · dsimp only; rw [f1 W hW, a1 W le_top]; ring
        · dsimp only; rw [f2 W hW, a2 W le_top]; ring
        · dsimp only; rw [f3 W W' hh hW, a3 W W' hh le_top, map_sub]
        · dsimp only; rw [fc W hW, kc, sub_zero]
      glue := fun k i i' O hO f => by
        have hle : O ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (h.j i) ⊓ Dd.toPre.P.L.U (h.j i')) := fun x hx =>
          ⟨h.le i (hO hx).1, h.le i' (hO hx).2⟩
        rw [opMod, opMod, h.glue k i i' O hO f, pb₂ _ _ O k f hle, hMg _ _ O k f hle, hc₁.2.2.2 _ _ O k f hle]
        ring }

  have wsm : ∀ (m : ℕ) (x y : Dd.toPre.X), w (m • x) y = (m : R) * w x y := by
    intro m x y
    induction m with
    | zero => simp only [zero_smul, Nat.cast_zero, zero_mul]; have := hw1 0 0 y; simp only [add_zero] at this; linear_combination -this
    | succ m ih => rw [succ_nsmul, hw1, ih]; push_cast; ring
  let e : ℕ → Dd.toPre.X → R := fun k α => -(2 * (k : R) * ℓ₂ α) - w α α - 2 * ℓ₁ α
  have key : ∀ k α σ σ', TActs Y h' k α σ σ' →
      TActs Y h k α σ (σ' - constFn Dd.toPre.P.A.hom ⊤ (e k α) • σ) := by
    rintro k α σ σ' ⟨τ, τ', hτ, hτ', hA⟩
    refine ⟨τ, τ' - constFn Y.H.hom ⊤ (e k α) • τ, hτ, _root_.GlobalTheory.HeatTermLin.isTerm_sub_smul R Dd.toPre O oa Y k α σ σ' τ τ' (e k α) hτ hτ',
      fun i => ?_⟩
    have hA' := hA i
    obtain ⟨V, hV⟩ := (hB i).1
    have hwt := _root_.GlobalTheory.HeatMod.isWt_fourierTerm R Dd.toPre O oa Y k α σ τ hτ (h.j i) (h.W i) ⟨V, hV⟩ (h.le i)
    change rsT (τ'.f fun _ => h.j i) (h.W i) = op Y.H dd (h.Θ + M) (h.u - c₁)
      (fun O f => h.d i O f - combF Y.H.hom dd c₂ O f) (h.p i) (h.p' i) k (h.W i)
      (rsT (τ.f fun _ => h.j i) (h.W i)) at hA'
    rw [opMod, wt₂ α _ ⟨V, hV⟩ _ hwt, hMa α _ ⟨V, hV⟩ _ hwt, hc₁.2.2.1 α _ ⟨V, hV⟩ _ hwt] at hA'
    have hle' : h.W i ≤ LB.wchart Dd.toPre.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => h.j i) := fun x hx =>
      Set.mem_iInter.2 fun _ => h.le i hx
    have hce : constFn Y.H.hom (h.W i) (e k α) = -(2 * (k : Γ(Y.H.left, h.W i)) * constFn Y.H.hom (h.W i) (ℓ₂ α)) -
        constFn Y.H.hom (h.W i) (w α α) - 2 * constFn Y.H.hom (h.W i) (ℓ₁ α) := by
      have hcf : ∀ a, constFn Y.H.hom (h.W i) a = ((Y.H.hom.appLE ⊤ (h.W i) (fun _ _ => trivial)).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) a := fun _ => rfl
      simp only [hcf, e, map_sub, map_neg, map_mul, map_natCast, map_ofNat]
    change rsT ((τ'.f fun _ => h.j i) - resG Y.H.left le_top (constFn Y.H.hom ⊤ (e k α)) * τ.f fun _ => h.j i) (h.W i) = _
    rw [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_mul, rsT_resG_constFn, hA', hce]
    · ring
    · exact hle'
  refine ⟨h', fun i => ?_, ?_⟩
  · obtain ⟨b1, b2, b3, b4⟩ := hB i
    refine ⟨b1, b2, b3, fun α V hV f hf => ?_⟩
    show IsWt Y α _ (h.d i _ f - combF Y.H.hom dd c₂ _ f)
    rw [wt₂ α _ ⟨V, rfl⟩ f hf]
    exact _root_.GlobalTheory.HeatMod.isWt_sub_const_mul R Dd.toPre O oa Y α _ _ f (ℓ₂ α) (b4 α V hV f hf) hf
  · intro k mu α σ σ' σ₁ σ₁' hk hS hT1 hT2
    have H := hD k mu α σ _ σ₁ _ hk hS (key _ _ _ _ hT1) (key _ _ _ _ hT2)
    have H2 := _root_.GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul R Dd.toPre k mu α σ σ' σ₁ σ₁' _ _ _ hS H
    convert H2 using 1
    exact defect_cancel w π π' half h2 hw1 hw2 hπ' hπ k mu α

end GlobalTheory.HeatMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.TraitPull

theorem exists_pull_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  intro E _ _ _ H Dw l Xo c T W _ _ _ hW hWd h hi hl
  obtain ⟨tW, ⟨m⟩⟩ := GlobalTheory.Models.Inhab.exists_pull (spMap h) T.t
  obtain ⟨PW, e, he⟩ := GlobalTheory.UnifDvrBaseChange.exists_pelUnif E H T.V T.cdvr T.t T.P W hW hWd h hi hl tW ⟨m⟩
  refine ⟨tW, m, PW, e, fun y => ?_⟩
  obtain ⟨u, n, hn, hc⟩ := T.mono (e y)
  have hn0 : T.be (e y) (e y) = 2 * (n 0 : ℤ) := hn 0
  obtain ⟨v, hv⟩ := he y _ hc
  refine ⟨by rw [hn0]; positivity, _, hv, ?_⟩
  have ht : (T.be (e y) (e y)).toNat = 2 * n 0 := by rw [hn0]; omega
  rw [ht]
  have hu : IsUnit ((v : W) * h u) := v.isUnit.mul (u.isUnit.map h)
  have e1 : ((v : W) * h (u * ∏ i, ![T.ϖ] i ^ n i)) ^ 2 = ((v : W) * h u) ^ 2 * h T.ϖ ^ (2 * n 0) := by
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
    ring
  rw [e1]
  exact associated_unit_mul_left _ _ (hu.pow 2)

end GlobalTheory.UPoinc.TraitPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionLocalVanishing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.Discrepancy

theorem exists_logRes_subsingleton_cohOn_one : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y) (N : CartierDiv X), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) ∧ (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) := by
  intro hPr X _ _ p n hp hn η m G Z hη hm hZ
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have hpS : IsProjOver (strHom ℂ (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hbig : IsBig ℂ H := IsAmpleLB.isBig ℂ X hpS H hH
  obtain ⟨Y, _, s, _, K, B, hlog, hZB, a, Fd, A, hA, hFd⟩ :=
    GlobalTheory.T.exists_log_resolution_big_bundle hPr ℂ X p n hp hn η m G hη Z hZ H hH.isLB hbig
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hlog.smooth
  haveI : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hlog.proj
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor ℂ Y (s ≫ p) n hlog.proj (pullCart s G - m • K) m

  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (hH.eventually_isAmpleLB_tens_lbPow_succ (isLB_toLB (-G)))
  have hj : J ≤ m * (J + 1) - 1 := by
    have : J + 1 ≤ m * (J + 1) := Nat.le_mul_of_pos_left _ hm
    omega
  have hTa := hJ _ hj
  have hsucc : m * (J + 1) - 1 + 1 = m * (J + 1) := by
    have : 1 ≤ m * (J + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' (Nat.succ_ne_zero J))
    omega
  rw [hsucc] at hTa
  obtain ⟨N, hNc⟩ := toPic_surjective ((J + 2) • cls H hH.isLB)
  have hTn : IsNef ℂ (tens (toLB (-G)) (lbPow H (m * (J + 1)))) := hTa.isNef
  have hcls : cls _ hTn.isLB = (m * 1) • cls (toLB N) (isLB_toLB N) - 1 • toPic G - m • cls H hH.isLB := by
    rw [cls_tens (isLB_toLB (-G)) (isLB_lbPow hH.isLB _), cls_lbPow hH.isLB, ← toPic_apply,
      ← toPic_apply, hNc, map_neg]
    simp only [mul_one, one_smul, smul_smul]
    rw [show m * (J + 2) = m * (J + 1) + m by ring, add_smul]
    abel
  obtain ⟨-, hloc⟩ := GlobalTheory.T.multiplier_vanishing_nef_twist_ample ℂ X p n hp η m G Y s K B F hη hm hlog hF (toLB N) H _
    (isLB_toLB N) hH.isLB 1 hTn one_pos hcls hH.isNef a Fd A hA hFd
  refine ⟨Y, inferInstance, inferInstance, s, inferInstance, K, B, F, N, hlog, hZB, hF,
    fun U hU => ?_⟩
  have hP := pull_isLB (isLB_toLB N) s
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule Y) (isLB_toLB (-F)) hP
    (isLB_toLB (pullCart s N - F)) (by
      rw [← toPic_apply, ← toPic_apply, cls_pull (isLB_toLB N) s hP, ← toPic_apply,
        ← toPic_pullCart, map_sub, map_neg]
      abel)
  exact (cohOn.mapIso Γ(Y, ⊤) (s ⁻¹ᵁ U) 1 e).toEquiv.subsingleton_congr.1 (hloc U hU 1 one_pos)

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusTorsionPointsAreLevelSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ g : Over.mk x₀ ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ g : Over.mk x ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g := by
  first | (exact @GlobalTheory.LevSurjOpen.exists_open_levSurj) | (exact GlobalTheory.LevSurjOpen.exists_open_levSurj) | (intros; apply GlobalTheory.LevSurjOpen.exists_open_levSurj  <;> assumption)
end

