module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDet
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AbsHalfLevi

theorem absHalf_det_div_eq_deltaHalf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) := by
  intro E _ _ _ a b w m
  rw [GlobalTheory.SmGL.deltaHalf_two, Units.val_mul]
  have e1 : m.1.val.det = ((GeneralLinearGroup.det m.1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  have e2 : m.2.val.det = ((GeneralLinearGroup.det m.2 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  rw [e1, e2]
  generalize GeneralLinearGroup.det m.1 = d1
  generalize GeneralLinearGroup.det m.2 = d2
  have n1 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d1
  have n2 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d2
  have hb : ((Fintype.card (Fin b) : ℂ) / 2) = (((b : ℝ) / 2 : ℝ) : ℂ) := by simp
  have ha : (-(Fintype.card (Fin a) : ℂ) / 2) = ((-(a : ℝ) / 2 : ℝ) : ℂ) := by simp
  rw [hb, ha, GlobalTheory.SmGL.val_absPow_ofReal, GlobalTheory.SmGL.val_absPow_ofReal, n1, n2, ← Complex.ofReal_mul]
  unfold absHalf
  congr 1
  have hd1 : ((d1 : w.adicCompletion E)) ≠ 0 := d1.ne_zero
  have hd2 : ((d2 : w.adicCompletion E)) ≠ 0 := d2.ne_zero
  have hx : ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  have hv1 : Valued.v (d1 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd1
  have hv2 : Valued.v (d2 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd2
  have hord : ordL ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) =
      -((b : ℤ) * WithZero.log (Valued.v (d1 : w.adicCompletion E)) - (a : ℤ) * WithZero.log (Valued.v (d2 : w.adicCompletion E))) := by
    have hv : Valued.v ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    unfold ordL
    rw [dite_eq_right hv, WithZero.toAdd_unzero_eq_log, map_div₀, map_pow, map_pow,
      WithZero.log_div (pow_ne_zero _ hv1) (pow_ne_zero _ hv2), WithZero.log_pow, WithZero.log_pow]
    simp
  rw [hord, neg_neg]
  have hq : (0 : ℝ) < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV; exact (Ideal.absNorm_eq_zero_iff).not.mpr w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  generalize WithZero.log (Valued.v (d1 : w.adicCompletion E)) = l1
  generalize WithZero.log (Valued.v (d2 : w.adicCompletion E)) = l2
  generalize (qV E w : ℝ) = q at hq ⊢
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

end GlobalTheory.AbsHalfLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultNsmulOfQadd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem mult_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    rw [zero_nsmul, (CartierDiv.isEqn_zero z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero]
    simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem qNum_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ (N : LB X) (a b : ℚ) (D B : X → ℚ), QNum p N a D → QNum p N b B →
      QNum p N (a + b) (D + B) := by
  intro X _ _ p hp N a b D B hD hB
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m, D₀, hm, hD₀, rfl, hDn⟩ := hD
  obtain ⟨m', B₀, hm', hB₀, rfl, hBn⟩ := hB
  refine ⟨m * m', m' • D₀ + m • B₀, Nat.mul_pos hm hm', (eff_nsmul_of_qadd hD₀ m').add
    (eff_nsmul_of_qadd hB₀ m), ?_, ?_⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul_of_qadd]
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    push_cast
    field_simp
  · intro C hC
    let hLB (D : CartierDiv X) : (toLB D).IsLB := (presents_toLB D).isLB
    let f : CartierDiv X →+ Pic X := AddMonoidHom.mk' (fun D => cls _ (hLB D)) fun D E =>
      (cls_eq_iff _ (isLB_tens (hLB D) (hLB E))).2
        ((presents_toLB _).lbIso ((presents_toLB D).tens (presents_toLB E)))
    have e := hC.interNumRed_of_cls_eq_add (N := toLB (m' • D₀ + m • B₀))
      (A := lbPow (toLB D₀) m') (B := lbPow (toLB B₀) m) hH (hLB (m' • D₀ + m • B₀))
      (isLB_lbPow (hLB D₀) m') (isLB_lbPow (hLB B₀) m)
      (by
        rw [cls_lbPow (hLB D₀), cls_lbPow (hLB B₀)]
        change f (m' • D₀ + m • B₀) = m' • f D₀ + m • f B₀
        rw [map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (hLB D₀), hC.interNumRed_lbPow hH (hLB B₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have hD' := hDn C hC
    have hB' := hBn C hC
    rw [e]
    push_cast
    rw [div_eq_iff h1] at hD'
    rw [div_eq_iff h2] at hB'
    rw [div_eq_iff (mul_ne_zero h1 h2), hD', hB']
    ring

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapExtremalVectorHolomorphicType
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultHol

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n}

omit [Fintype ι] [DecidableEq ι] in
theorem one_mem_UG : (1 : ι → Mt n) ∈ UG Hm := fun τ => by
  show (1 : Mt n)ᴴ * Hm τ * 1 = Hm τ
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem mul_mem_UG {u u' : ι → Mt n} (hu : u ∈ UG Hm) (hu' : u' ∈ UG Hm) : u * u' ∈ UG Hm := fun τ => by
  have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  have h2 : (u' τ)ᴴ * Hm τ * u' τ = Hm τ := hu' τ
  show (u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = Hm τ
  calc _ = (u' τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * u' τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm τ := by rw [h1, h2]

omit [Fintype ι] in
theorem mulSingle_mem_UG (τ : ι) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH (Hm τ)) :
    (Pi.mulSingle τ g : ι → Mt n) ∈ UG Hm := fun ρ => by
  by_cases h : ρ = τ
  · subst h; simpa using hg
  · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_UG (Hm := Hm) ρ

omit [Fintype ι] [DecidableEq ι] in
theorem lift_prod {G : Type} [Group G] (L : (ι → Mt n) → G)
    (hL : ∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, L (u * u') = L u * L u') (l : List (ι → Mt n)) (hl : ∀ u ∈ l, u ∈ UG Hm) :
    l.prod ∈ UG Hm ∧ L l.prod = (l.map L).prod := by
  induction l with
  | nil =>
    refine ⟨one_mem_UG, ?_⟩
    have h := hL 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    simpa using h
  | cons a l ih =>
    have ha := hl a (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih fun u hu => hl u (List.mem_cons_of_mem _ hu)
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact ⟨mul_mem_UG ha h1, by rw [hL a ha _ h1, h2]⟩

theorem parts_mem_lieH {G : Mt n} (hh : G.IsHermitian) (hd : G.det ≠ 0) (Z : Mt n) :
    (1 / 2 : ℂ) • (Z + conjH G Z) ∈ lieH G ∧ (1 / (2 * Complex.I)) • (Z - conjH G Z) ∈ lieH G := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hd
  have e1 : G * conjH G Z = -(Zᴴ * G) := by
    rw [conjH, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have e2 : (conjH G Z)ᴴ * G = -(G * Z) := by
    have := congrArg conjTranspose e1
    simpa only [conjTranspose_mul, conjTranspose_neg, conjTranspose_conjTranspose, hh.eq] using this
  constructor
  · show _ + _ = _
    have s : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, s, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, e1, e2]
    simp
  · show _ + _ = _
    have s : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp
    rw [conjTranspose_smul, s, Matrix.smul_mul, Matrix.mul_smul, neg_smul, ← smul_neg, ← smul_add, conjTranspose_sub,
      Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    have : -(Zᴴ * G - -(G * Z)) + (G * Z - -(Zᴴ * G)) = 0 := by abel
    rw [this, smul_zero]

end Local

theorem holAd_of_isMultMap : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → HolAd θ M w (T v) := by
  classical
  intro D θ V S M w v hθ hS hw hv J χ T hT g
  obtain ⟨L, -, hmul, -, -, hinv, hat, -, -, hG⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hexp : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun τ X hX t => GlobalTheory.SmVec.exp_mem_UH ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hG τ).2)) hX t
  have hone : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ,
      L (Pi.mulSingle τ (NormedSpace.exp (t • X))) = oneP θ V τ X t :=
    fun τ X hX t => (hat τ _ (hexp τ X hX t)).symm
  refine ⟨fun u => T v (g * L u), ?_, fun u hu => by simp only [hinv u hu]⟩
  refine _root_.GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ (fun τ => ((_root_.GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.2.2 hS).1) _ ?_ ?_
  · intro k τs Xs hX u hu
    have h := (hT.aut v).smooth k τs Xs hX (g * L u)
    convert h using 2 with t
    obtain ⟨h1, h2⟩ := lift_prod L hmul
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact mulSingle_mem_UG _ (hexp _ _ (hX i) _))
    show T v (g * L (u * _)) = _
    rw [hmul u hu _ h1, h2, List.map_ofFn, mul_assoc]
    exact congrArg (fun F : Fin k → GA D V => T v (g * (L u * (List.ofFn F).prod))) (funext fun i => hone _ _ (hX i) _)
  · intro τ a c hac u hu
    have hder : ∀ X ∈ lieH (gramAt D V τ), der τ X (fun u => T v (g * L u)) u = Rder θ V τ X (T v) (g * L u) := by
      intro X hX
      unfold der Rder
      congr 1
      funext t
      show T v (g * L (u * _)) = _
      rw [hmul u hu _ (mulSingle_mem_UG _ (hexp _ _ hX _)), hone τ X hX, mul_assoc]
    obtain ⟨p1, p2⟩ := parts_mem_lieH (hG τ).1 (hG τ).2 (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹)
    have hk := (GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hS hw hv τ).2 a c hac
    have hd := _root_.GlobalTheory.MultDer.rderC_eq D θ V hθ S M J χ T hT v τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹)
      (if a = c then (w τ a : ℂ) • v τ else 0) (by rw [hk]; split_ifs <;> rfl)
    have e : derC (gramAt D V) τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (fun u => T v (g * L u)) u =
        RderC θ V τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (T v) (g * L u) := by
      unfold derC
      rw [hder _ p1, hder _ p2]
      rfl
    rw [e, hd]
    split_ifs
    · rw [T.map_update_smul, Function.update_eq_self]
      rfl
    · rw [T.map_update_zero]
      rfl

end GlobalTheory.MultHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {B N P : LB X}

theorem IsNef.topSelf_le_of_cls_eq_add (h : Published.NefProductNonneg)
    (hp : IsProjOver (strHom k (X := X))) {D : ℕ} (hD : topologicalKrullDim X = D)
    (hB : IsNef k B) (hN : IsNef k N) (hP : P.IsLB)
    (e : cls P hP = cls B hB.isLB + cls N hN.isLB) : topSelfIntersection k B D ≤ topSelfIntersection k P D := by
  classical
  have hf := algebraMap_eq_strHom k X
  have hS : QCoh.suppDim (structureModule X) ≤ D := by
    unfold QCoh.suppDim
    exact (topologicalKrullDim_subspace_le X _).trans hD.le
  have hV := diffVanish_chiPic_of_isProjOver hf (structureModule X) hp hS
  have hL : ∀ j : Fin 2, ((![B, N] : Fin 2 → LB X) j).IsLB := by
    intro j; fin_cases j
    · exact hB.isLB
    · exact hN.isLB
  have hQ : ∀ _ : Fin D, P.IsLB := fun _ => hP
  have hexp := hV.interNum_of_cls_eq_sum hL hQ (fun _ _ => (1 : ℤ)) (by
    intro _
    simp [Fin.sum_univ_two, e])
  have hnn : ∀ a : Fin D → Fin 2, 0 ≤ interNum k (structureModule X) ((![B, N] : Fin 2 → LB X) ∘ a) := by
    intro a
    refine h.interNum_nonneg hp hD ?_
    intro i
    show IsNef k (![B, N] (a i))
    generalize a i = j
    fin_cases j
    · exact hB
    · exact hN
  rw [topSelf_def, topSelf_def, hexp]
  simp only [Finset.prod_const_one, one_mul]
  have h0 := Finset.single_le_sum (fun a _ => hnn a) (Finset.mem_univ (fun _ : Fin D => (0 : Fin 2)))
  exact h0

theorem IsBig.of_cls_eq_add_nef (h : Published.NefNumerics) (hp : IsProjOver (strHom k (X := X)))
    (hb : IsBig k B) (hB : IsNef k B) (hN : IsNef k N) (hP : P.IsLB)
    (e : cls P hP = cls B hB.isLB + cls N hN.isLB) : IsBig k P := by
  obtain ⟨D, hD, -⟩ := hb.growth
  have hf := algebraMap_eq_strHom k X
  have hT : (CechPic.tens B N).IsLB := CechPic.isLB_tens hB.isLB hN.isLB
  have hTn : IsNef k (CechPic.tens B N) := IsNef.tens_of_isProjOver hB hN hp
  have hPn : IsNef k P := hTn.of_cls_eq hP (by rw [e, CechPic.cls_tens hB.isLB hN.isLB])
  have hle := IsNef.topSelf_le_of_cls_eq_add h.1 hp hD hB hN hP e
  have hpos : 0 < topSelfIntersection k B D := (h.2.2.isBig_iff hp hD hB).1 hb
  exact (h.2.2.isBig_iff hp hD hPn).2 (lt_of_lt_of_le hpos hle)

theorem IsBig.tens_nef (h : Published.NefNumerics) (hp : IsProjOver (strHom k (X := X)))
    (hb : IsBig k B) (hB : IsNef k B) (hN : IsNef k N) : IsBig k (CechPic.tens B N) := by
  have hT : (CechPic.tens B N).IsLB := CechPic.isLB_tens hB.isLB hN.isLB
  exact IsBig.of_cls_eq_add_nef h hp hb hB hN hT (CechPic.cls_tens hB.isLB hN.isLB hT)

theorem IsNef.isBig_tens_ample [IsIntegral X] (h : Published.NefNumerics)
    (hp : IsProjOver (strHom k (X := X))) (hN : IsNef k N) (hB : IsAmpleLB B) :
    IsBig k (CechPic.tens N B) := by
  have hT : (CechPic.tens N B).IsLB := CechPic.isLB_tens hN.isLB hB.isLB
  have hbig : IsBig k B := IsAmpleLB.isBig k X hp B hB
  exact IsBig.of_cls_eq_add_nef h hp hbig hB.isNef hN hT
    (by rw [CechPic.cls_tens hN.isLB hB.isLB hT, add_comm])

theorem IsNef.isPsEff : Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ N : LB X, IsNef k N → IsPsEff N := by
  intro h k _ X _ _ hp N hN
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  refine ⟨hN.isLB, A, hA, fun m hm => ?_⟩
  have hNm : IsNef k (lbPow N m) := hN.pow hA m
  have hbig : IsBig k (CechPic.tens (lbPow N m) A) := IsNef.isBig_tens_ample h hp hNm hA
  obtain ⟨r, hr, hs⟩ := (hbig.frequently_hasNonzeroSec.and_eventually (Filter.eventually_ge_atTop 1)).exists
  exact ⟨r, hs, hr⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEmbeddingEntryDefiniteUnitaryRationalPointLe
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  set M : Matrix (Fin n) (Fin n) E := (γ : GL (Fin n) E).val with hM
  have h : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * 1 * M = 1 := γ.2
  rw [Matrix.mul_one] at h
  have hjj : ∑ k, IsCMField.complexConj E (M k j) * M k j = 1 := by
    have := congrFun₂ h j j
    simpa [Formalism.UG.cT, Matrix.mul_apply] using this
  have hτ : ∑ k, ((Complex.normSq (τ (M k j)) : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.normSq_eq_conj_mul_self]
  have hR : ∑ k, Complex.normSq (τ (M k j)) = 1 := by exact_mod_cast hτ
  have hle : Complex.normSq (τ (M i j)) ≤ 1 := by
    rw [← hR]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (τ (M k j))) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  have hsq : ‖τ (M i j)‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

end GlobalTheory.BCT.FinPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitOffDiagonalTransitionOnCommonSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.OnSection

theorem not_unitAt_of_eq {F : Type} [Field F] {X Y : Var F} {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) (W : Dbl Y)
    (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) (τ : ι) (a b : Fin (m τ)) (hab : a ≠ b) {k : Type} [Field k]
    (w : Sp k ⟶ W.Z) (hw : w ≫ W.p₁ = w ≫ W.p₂) (A : Mat m Y.Fn)
    (hA : A ∈ E'.S (W.p₁ (w (IsLocalRing.closedPoint k)))) :
    ¬ UnitAt (w (IsLocalRing.closedPoint k)) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨ev, hev, hq⟩ := _root_.GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint F Y W.Z k w
  have hp : W.p₂ (w (IsLocalRing.closedPoint k)) = W.p₁ (w (IsLocalRing.closedPoint k)) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun q : Sp k ⟶ Y.X => q (IsLocalRing.closedPoint k)) hw.symm).trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨A₀, hA₀⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hM := hf.sub _ A hA A₀ hA₀
  have hd : ∀ σ, (A₀.map φ σ).det ≠ 0 := fun σ => by
    have := Mat.det_map A₀ (φ : X.Fn →+* Y.Fn) σ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA₀ σ))
  generalize hB : A₀.map φ = B at hM hd
  have hB12 : B.map W.α₁ = B.map W.α₂ := by
    subst hB
    funext σ
    ext i j
    exact hα _
  have h1 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₁ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => hq W.p₁ u (mem_O_ratOf.1 hu)
  have h2 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₂ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => by
    obtain ⟨h, e⟩ := hq W.p₂ u (by rw [hp]; exact mem_O_ratOf.1 hu)
    exact ⟨h, e.trans (congrArg (fun q => (ratOf Y).val q u) hw.symm)⟩
  have hN₁ := hM.map W.α₁ fun u hu => (h1 u hu).choose
  have hN₂ := hM.map W.α₂ fun u hu => (h2 u hu).choose
  have hd₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => (Mat.det_map B W.α₂ σ).trans_ne ((map_ne_zero _).2 (hd σ))
  have hg : A.map W.α₁ * (A.map W.α₂)⁻¹ = (A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hB12, Mat.mul_inv_rev, Mat.inv_inv hd₂, mul_assoc,
      ← mul_assoc _ (B.map W.α₂), Mat.inv_mul hd₂, one_mul]
  rw [hg]
  have hG := hN₁.mul hN₂.inv
  let v : W.Z.functionField → k := fun u => if h : u ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k)))
    W.Z.functionField).range then ev ⟨u, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v (x : W.Z.functionField) = ev x := fun x => dif_pos x.2
  have e1 := Par.map_mul_of hG hN₂ v ev hv
  rw [mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one] at e1
  have e2 : ((A * B⁻¹).map W.α₁).map v = ((A * B⁻¹).map W.α₂).map v := by
    funext σ
    ext i j
    obtain ⟨p, hp⟩ := h1 _ ((hM σ).1 i j)
    obtain ⟨q, hq⟩ := h2 _ ((hM σ).1 i j)
    exact ((hv ⟨_, p⟩).trans hp).trans ((hv ⟨_, q⟩).trans hq).symm
  have hV := (Par.map_of hN₂ v ev hv).det_ne
  have e3 : ((A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹).map v = 1 := by
    have := congrArg (· * (((A * B⁻¹).map W.α₂).map v)⁻¹) (e1.symm.trans e2)
    simpa only [mul_assoc, Mat.mul_inv hV, mul_one] using this
  intro hu
  refine (hev ⟨_, (hG τ).1 a b⟩).2 hu ((hv ⟨_, (hG τ).1 a b⟩).symm.trans ?_)
  exact (congrFun (congrFun (congrFun e3 τ) a) b).trans (Matrix.one_apply_ne hab)

end GlobalTheory.FlagPush.OnSection

theorem GlobalTheory.FlagPush.not_unitAt_section : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), a ≠ b → ∀ y : Y.X, ∀ A ∈ E'.S y, ¬ UnitAt (W.δ y) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b hab y A hA
  let w₀ : Sp (Y.X.residueField y) ⟶ Y.X := Y.X.fromSpecResidueField y
  have h0 : w₀ (IsLocalRing.closedPoint _) = y := Scheme.fromSpecResidueField_apply _ _
  have h1 : (w₀ ≫ W.δ) (IsLocalRing.closedPoint _) = W.δ y := (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ h0)
  have h2 : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
  have := OnSection.not_unitAt_of_eq hf W hα τ a b hab (w₀ ≫ W.δ)
    (by rw [Category.assoc, Category.assoc, W.δ₁, W.δ₂]) A (by rw [h1, h2]; exact hA)
  rwa [h1] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermRealTrivialisation
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_term_real_trivialisation : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  first | (exact @GlobalTheory.LKCx.finite_minpoly_fix_a_one) | (exact GlobalTheory.LKCx.finite_minpoly_fix_a_one) | (intros; apply GlobalTheory.LKCx.finite_minpoly_fix_a_one  <;> assumption)
end

