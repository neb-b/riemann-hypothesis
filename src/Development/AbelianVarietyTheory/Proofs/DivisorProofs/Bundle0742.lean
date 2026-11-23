module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarSpecialUnitaryLyingOverFlagDomain
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates Topology
open scoped ENNReal

namespace GlobalTheory.SUHaarOver

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_det_eq_one (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x)
    {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hn : X.IsUnitaryC n) (τ : X.Ψ) : ‖(n τ).det‖ = 1 := by
  have h := UnitaryInvMeasure.gram_lmulC X hn x τ
  have hm : mat (X.lmulC n x) τ = n τ * mat x τ := rfl
  rw [hm, UnitaryFrames.gram_eq_mul, UnitaryFrames.gram_eq_mul] at h
  have hd := congrArg Matrix.det h
  have hK : (mat x τ).det * ((X.Gm.map τ.1).det * ((mat x τ).map (starRingEnd ℂ)).det) ≠ 0 := by
    have h2 := congrArg Matrix.det (hx τ)
    rw [UnitaryFrames.gram_eq_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
    rw [h2, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    unfold sgn
    split_ifs <;> simp
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.map_mul] at hd
  have hc : ((n τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (n τ).det := (RingHom.map_det _ _).symm
  rw [hc] at hd
  have h3 : (n τ).det * (starRingEnd ℂ) (n τ).det = 1 := by
    apply mul_right_cancel₀ hK
    linear_combination hd
  have h4 : ((Complex.normSq (n τ).det : ℝ) : ℂ) = 1 := by rw [← Complex.mul_conj]; exact h3
  have h5 : Complex.normSq (n τ).det = 1 := by exact_mod_cast h4
  rw [Complex.normSq_eq_norm_sq] at h5
  have h6 : 0 ≤ ‖(n τ).det‖ := norm_nonneg _
  nlinarith [h5, h6]


open UnitaryInvMeasure in
theorem exists_haar_lying_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)], 1 ≤ r → IsOrth X x →
    ∃ ν : Measure (realSU X.Ψ X.Gm), ν.IsHaarMeasure ∧ ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ →
      (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) →
      ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν =
        ∫⁻ z, φ (cpt X x z) ∂muF X x := by
  intro E _ _ _ r X x _ _ hr hx
  classical
  set H := UnitaryFrames.unitarySubgroup X with hHdef
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  have hHm : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ) := fun _ => Iff.rfl
  obtain ⟨hLC, hSC, hfr⟩ := UnitaryFrames.unitary_group_frames.2 r X H hHm
  haveI := hLC
  haveI := hSC
  obtain ⟨-, ι, hιc, hι1, -⟩ := hfr x hx
  obtain ⟨νU, hνl, hνf, hν⟩ := invMeas FrameMeasureClosed.measure_statements.2.1
    GramSchmidtCont.exists_continuous_gramSchmidt isOrth_rmul_iff_unitary_diagonal
    (SatFin.muF_sat_lt_top FrameMeasureClosed.measure_statements.2.1)
    UnitaryFrames.unitary_group_frames.2 r X H hHm x hx
  haveI := hνl
  haveI := hνf
  let M : (X.Ψ → GL (Fin r) ℂ) → X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun g τ => (g τ : Matrix (Fin r) (Fin r) ℂ)
  have hU : ∀ g : H, X.IsUnitaryC (M g.1) := fun g => g.2
  have hMmul : ∀ g h : X.Ψ → GL (Fin r) ℂ, ∀ τ, M (g * h) τ = M g τ * M h τ := fun g h τ => by
    simp only [M, Pi.mul_apply, Units.val_mul]
  have hMc : ∀ τ, Continuous fun g : X.Ψ → GL (Fin r) ℂ => M g τ := fun τ =>
    Units.continuous_val.comp (continuous_apply τ)

  let dC : H → X.Ψ → Circle := fun g τ =>
    ⟨(M g.1 τ).det, by simpa [Submonoid.unitSphere] using norm_det_eq_one X hx (hU g) τ⟩
  have hdC : ∀ g τ, ((dC g τ : Circle) : ℂ) = (M g.1 τ).det := fun _ _ => rfl
  let tU : H → Torus X := fun g τ a => if (a : ℕ) = 0 then (dC g τ)⁻¹ else 1
  let cT : Torus X → H := fun t => ι (rmul x (diagF X t))
  let cU : H → H := fun g => cT (tU g)
  have horthT : ∀ t, IsOrth X (rmul x (diagF X t)) := fun t =>
    (isOrth_rmul_iff_unitary_diagonal r X x _ hx (diagF_mem X t)).2 (diagF_unit X t)
  have hcx : ∀ t, X.lmulC (M (cT t).1) x = rmul x (diagF X t) := fun t => hι1 _ (horthT t)

  have hdCc : Continuous dC := continuous_pi fun τ =>
    Continuous.subtype_mk ((hMc τ).comp continuous_subtype_val).matrix_det _
  have htUc : Continuous tU := by
    refine continuous_pi fun τ => continuous_pi fun a => ?_
    by_cases ha : (a : ℕ) = 0
    · simp only [tU, ha, if_true]
      exact ((continuous_apply τ).comp hdCc).inv
    · simp only [tU, ha, if_false]
      exact continuous_const
  have hcTc : Continuous cT := by
    refine hιc.comp_continuous ?_ fun t => horthT t
    exact (continuous_rmul X).comp (continuous_const.prodMk (continuous_diagF X))
  have hcUc : Continuous cU := hcTc.comp htUc

  have hdetc : ∀ (g : H) τ, (M (cU g).1 τ).det * (M g.1 τ).det = 1 := by
    intro g τ
    have h1 := congrArg Matrix.det (congrFun (hcx (tU g)) τ)
    have e1 : X.lmulC (M (cU g).1) x τ = M (cU g).1 τ * mat x τ := rfl
    have e2 : rmul x (diagF X (tU g)) τ = mat x τ * mat (diagF X (tU g)) τ := rfl
    have e3 : (mat (diagF X (tU g)) τ).det = ((M g.1 τ).det)⁻¹ := by
      show (Matrix.diagonal fun a => ((tU g τ a : Circle) : ℂ)).det = _
      rw [Matrix.det_diagonal, Finset.prod_eq_single (⟨0, hr⟩ : Fin r)]
      · simp only [tU, if_true, Circle.coe_inv, hdC]
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
        simp only [tU, this, if_false, Circle.coe_one]
      · simp
    have hx0 := UnitaryFrames.det_ne_zero_of_isOrth X hx τ
    have hg0 : (M g.1 τ).det ≠ 0 := by
      intro h0
      have := norm_det_eq_one X hx (hU g) τ
      rw [h0, norm_zero] at this
      exact zero_ne_one this

    have h2 : (M (cU g).1 τ).det * (mat x τ).det = (mat x τ).det * ((M g.1 τ).det)⁻¹ := by
      have h1' : (M (cU g).1 τ * mat x τ).det = (mat x τ * mat (diagF X (tU g)) τ).det := by
        rw [← e1, ← e2]; exact h1
      rw [Matrix.det_mul, Matrix.det_mul, e3] at h1'
      exact h1'
    have hi : (M g.1 τ).det * ((M g.1 τ).det)⁻¹ = 1 := mul_inv_cancel₀ hg0
    have h3 : (M (cU g).1 τ).det * (M g.1 τ).det = 1 := by
      apply mul_right_cancel₀ hx0
      linear_combination (M g.1 τ).det * h2 + (mat x τ).det * hi
    exact h3

  have hpmem : ∀ g : H, (g * cU g).1 ∈ realSU X.Ψ X.Gm := by
    intro g τ
    refine ⟨?_, (g * cU g).2 τ⟩
    show (M (g.1 * (cU g).1) τ).det = 1
    rw [hMmul, Matrix.det_mul, mul_comm]
    exact hdetc g τ
  let p : H → realSU X.Ψ X.Gm := fun g => ⟨(g * cU g).1, hpmem g⟩
  have hpc : Continuous p :=
    Continuous.subtype_mk (continuous_subtype_val.comp (continuous_id.mul hcUc)) _
  have hpm : Measurable p := hpc.measurable

  let incl : realSU X.Ψ X.Gm → H := fun s => ⟨s.1, fun τ => (s.2 τ).2⟩
  have hinclc : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  have hpinv : ∀ (s : (realSU X.Ψ X.Gm)) (g : H), p (incl s * g) = s * p g := by
    intro s g
    have htU : tU (incl s * g) = tU g := by
      have hd : dC (incl s * g) = dC g := by
        funext τ
        apply Subtype.ext
        show (M (s.1 * g.1) τ).det = (M g.1 τ).det
        rw [hMmul, Matrix.det_mul, (s.2 τ).1, one_mul]
      funext τ a
      show (if (a : ℕ) = 0 then (dC (incl s * g) τ)⁻¹ else 1) = (if (a : ℕ) = 0 then (dC g τ)⁻¹ else 1)
      rw [hd]
    apply Subtype.ext
    show (incl s * g).1 * (cT (tU (incl s * g))).1 = s.1 * (g.1 * (cT (tU g)).1)
    rw [htU, Subgroup.coe_mul, mul_assoc]

  have hkey : ∀ g : H, X.lmulC (M (g * cU g).1) x = rmul (X.lmulC (M g.1) x) (diagF X (tU g)) := by
    intro g
    funext τ
    have hc := congrFun (hcx (tU g)) τ
    show M ((g : X.Ψ → GL (Fin r) ℂ) * (cU g).1) τ * mat x τ = (M g.1 τ * mat x τ) * mat (diagF X (tU g)) τ
    have hc' : M (cU g).1 τ * mat x τ = mat x τ * mat (diagF X (tU g)) τ := hc
    rw [hMmul, Matrix.mul_assoc, hc', Matrix.mul_assoc]

  set ν : Measure (realSU X.Ψ X.Gm) := νU.map p with hνdef
  have hνinv : ν.IsMulLeftInvariant := ⟨fun s => by
    have hm1 : Measurable fun h : realSU X.Ψ X.Gm => s * h := (continuous_const.mul continuous_id).measurable
    have hm2 : Measurable fun h : H => incl s * h := (continuous_const.mul continuous_id).measurable
    rw [hνdef, Measure.map_map hm1 hpm,
      show (fun h => s * h) ∘ p = p ∘ (fun h => incl s * h) from funext fun g => (hpinv s g).symm,
      ← Measure.map_map hpm hm2, map_mul_left_eq_self]⟩
  have hνfin : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hνdef, Measure.map_apply hpm hK.measurableSet]
    have hC : IsCompact (Set.range cT) := isCompact_range hcTc
    have hK' : IsCompact (incl '' K) := hK.image hinclc
    refine lt_of_le_of_lt (measure_mono ?_) (hK'.mul hC.inv).measure_lt_top
    intro g hg
    refine Set.mem_mul.2 ⟨incl (p g), ⟨p g, hg, rfl⟩, (cU g)⁻¹, Set.inv_mem_inv.2 ⟨tU g, rfl⟩, ?_⟩
    have : incl (p g) = g * cU g := rfl
    rw [this, mul_inv_cancel_right]⟩
  have huniv : ν Set.univ = muF X x Set.univ := by
    have h1 := hν (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)
    simp only [lintegral_const, one_mul] at h1
    rw [hνdef, Measure.map_apply hpm MeasurableSet.univ, Set.preimage_univ, h1]
  haveI := hνinv
  haveI := hνfin
  have hs := Measure.isMulLeftInvariant_eq_smul ν (Measure.haar : Measure (realSU X.Ψ X.Gm))
  have hc0 : ν.haarScalarFactor (Measure.haar : Measure (realSU X.Ψ X.Gm)) ≠ 0 := by
    intro h0
    apply FlagQuotHaar.muF_univ_ne_zero X hx
    rw [← huniv, hs, h0, zero_smul, Measure.coe_zero, Pi.zero_apply]
  refine ⟨ν, ?_, fun φ hφ hφb => ?_⟩
  · rw [hs, ENNReal.smul_def]
    exact Measure.IsHaarMeasure.smul _ (ENNReal.coe_ne_zero.2 hc0) ENNReal.coe_ne_top
  · have hLc : Continuous fun g : realSU X.Ψ X.Gm =>
        X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x := by
      refine continuous_pi fun τ => ?_
      exact ((hMc τ).comp continuous_subtype_val).matrix_mul continuous_const
    have hm : Measurable fun g : realSU X.Ψ X.Gm =>
        φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) :=
      hφ.comp hLc.measurable
    rw [hνdef, lintegral_map hm hpm, ← hν φ hφ hφb]
    refine lintegral_congr fun g => ?_
    show φ (X.lmulC (M (g * cU g).1) x) = φ (X.lmulC (M g.1) x)
    rw [hkey g]
    exact hφb _ (IC.orth_mem_dom X (orth_lmulC X (hU g) hx)) _ (diagF_mem X _)

end

end GlobalTheory.SUHaarOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.BaseChange

open ReciprocityTheory.ChartRestriction.G.Pdiv

section SlopeTestRemainingChoices

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def OActN.pull {O : Type} [Ring O] {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OActN O G) :
    OActN O ((Over.pullback f).obj G) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

theorem OActN.pull_left {O : Type} [Ring O] {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OActN O G) (c : O) :
    ((OActN.pull f a).act c).left ≫ PullbackComparison.pφ f G = PullbackComparison.pφ f G ≫ (a.act c).left :=
  PullbackComparison.pullback_map_left_fst' f (a.act c)

theorem lift_pφ₂ {G : Over S} [GrpObj G] [IsCommMonObj G] {T' : Over S'} {T : Over S} (τ : T'.left ⟶ T.left)
    (a b : T' ⟶ (Over.pullback f).obj G) (a₀ b₀ : T ⟶ G)
    (ha : a.left ≫ PullbackComparison.pφ f G = τ ≫ a₀.left) (hb : b.left ≫ PullbackComparison.pφ f G = τ ≫ b₀.left) :
    (lift a b).left ≫ PullbackComparison.pφ₂ f G = τ ≫ (lift a₀ b₀).left := by
  apply PullbackComparison.adelic_GL2_ext_of_local_components
  · rw [Category.assoc, PullbackComparison.pφ₂_fst, ← Category.assoc, ← Over.comp_left, lift_fst, ha, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, PullbackComparison.pφ₂_snd, ← Category.assoc, ← Over.comp_left, lift_snd, hb, Category.assoc,
      ← Over.comp_left, lift_snd]

end SlopeTestRemainingChoices

section Aux2

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def tateMoveO {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : TateIsoO D k Q act e) : TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem isTanScal_push {O : Type} [Ring O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OActN O G) (a' : OActN O G')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ G') ≃* (epsPtR (x ≫ f) ⟶ G)) (he : ∀ v, (e v).left = v.left ≫ φ) (b : O) (c : R')
    (v : epsPtR x ⟶ G') : IsTanScal a' x b c v ↔ IsTanScal a (x ≫ f) b c (e v) := by
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · have E : e (v ≫ a'.act b) = e v ≫ a.act b := Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    rw [← E, he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ a'.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem secPull_comp {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (u : G ⟶ G) (u' : G' ⟶ G') (hu : u'.left ≫ φ = φ ≫ u.left)
    (s : 𝟙_ (Over S) ⟶ G) : GlobalTheory.ObjPull.secPull h (s ≫ u) = GlobalTheory.ObjPull.secPull h s ≫ u' := by
  apply Over.OverMorphism.ext
  refine h.1.hom_ext ?_ ?_
  · rw [GlobalTheory.ObjPull.secPull_left]
    simp only [Over.comp_left, Category.assoc]
    rw [hu, ← Category.assoc (Over.Hom.left _) φ, GlobalTheory.ObjPull.secPull_left, Category.assoc]
  · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]

end Aux2

section Ker

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem gen_ker_push {G : Over S} [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (T : Over S')
    (x : T ⟶ (Over.pullback f).obj G)
    (H : ∃ t : ((P.pull (PullbackComparison.pφ₂ f G)).pull
      (lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd G (Over.mk (T.hom ≫ f)) ≫ GlobalTheory.ObjPull.pushEquiv (PullbackComparison.isGrpPullback f G) T x)
      (fst G (Over.mk (T.hom ≫ f)))).left).Gen, t.IsGen := by
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let Z : Over S' := Over.mk ((snd G T₀).left ≫ T.hom)
  have hZ : (fst G T₀).left ≫ G.hom = Z.hom ≫ f :=
    (Over.w (fst G T₀)).trans ((Over.w (snd G T₀)).symm.trans (Category.assoc _ _ _).symm)
  let a : Z ⟶ (Over.pullback f).obj G := Over.homMk (pullback.lift (fst G T₀).left Z.hom hZ) (pullback.lift_snd _ _ _)
  let u : Z ⟶ T := Over.homMk (snd G T₀).left rfl
  have key : (lift (snd G T₀ ≫ GlobalTheory.ObjPull.pushEquiv (PullbackComparison.isGrpPullback f G) T x) (fst G T₀)).left =
      (lift a u).left ≫ ((lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left ≫
        PullbackComparison.pφ₂ f G) := by
    apply PullbackComparison.adelic_GL2_ext_of_local_components
    · have k1 := congrArg Over.Hom.left (show lift a u ≫ lift (snd ((Over.pullback f).obj G) T ≫ x)
          (fst ((Over.pullback f).obj G) T) ≫ fst ((Over.pullback f).obj G) ((Over.pullback f).obj G) = u ≫ x by simp)
      simp only [Over.comp_left] at k1
      rw [← Over.comp_left, lift_fst, Category.assoc, Category.assoc, PullbackComparison.pφ₂_fst,
        ← Category.assoc (Over.Hom.left (lift (snd ((Over.pullback f).obj G) T ≫ x) _)), ← Category.assoc, k1]
      rfl
    · have k2 := congrArg Over.Hom.left (show lift a u ≫ lift (snd ((Over.pullback f).obj G) T ≫ x)
          (fst ((Over.pullback f).obj G) T) ≫ snd ((Over.pullback f).obj G) ((Over.pullback f).obj G) = a by simp)
      simp only [Over.comp_left] at k2
      rw [← Over.comp_left, lift_snd, Category.assoc, Category.assoc, PullbackComparison.pφ₂_snd,
        ← Category.assoc (Over.Hom.left (lift (snd ((Over.pullback f).obj G) T ≫ x) _)), ← Category.assoc, k2]
      exact (pullback.lift_fst _ _ _).symm
  obtain ⟨t, ht⟩ := H
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullIn P (fun _ : PUnit => PullbackComparison.pφ₂ f G) (fun _ => 1)
    (lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left) t ht
  exact gen_chartPull (chartPullSame P _ _ (fun _ : PUnit => 1) (lift a u).left (fun _ => key)) t₁ ht₁

end Ker

theorem exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (f : S' ⟶ S), f ≫ s = s' →
    ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  intro p _ D R _ b N S S' s s' o f hs
  subst hs
  have h : IsGrpPullback ((Over.pullback f).obj o.A) o.A f (PullbackComparison.pφ f o.A) := PullbackComparison.isGrpPullback f o.A
  have hact := OActN.pull_left f o.act
  have hP := pull_isLB o.isLB (PullbackComparison.pφ₂ f o.A)
  have hL := pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left
  have hL' := pull_isLB hP (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left
  have hdiag : (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left ≫ PullbackComparison.pφ₂ f o.A =
      PullbackComparison.pφ f o.A ≫ (lift (𝟙 o.A) (𝟙 o.A)).left :=
    lift_pφ₂ f _ _ _ _ _ (by simp) (by simp)
  have hLi : LBIso ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull
      (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left)
      ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull (PullbackComparison.pφ f o.A)) :=
    LBIso.chartPull (chartPullLinComb o.P (PullbackComparison.pφ₂ f o.A) _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ f o.A) (fun _ => hdiag))
      (chartPullPull _ (PullbackComparison.pφ f o.A) _ rfl) (PullbackComparison.gen_refl _ hL)
  obtain ⟨hab, hamp, -⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' o.A _ f _
    _ _ hL hL' o.ab h hLi
  have hrose : ∀ c : D.O, LBIso ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull
      (lift (fst ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A) ≫ (OActN.pull f o.act).act c)
        (snd ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A))).left)
      ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull (lift (fst ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A))
        (snd ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A) ≫
          (OActN.pull f o.act).act (D.star c).unop)).left) := fun c => by
    refine LBIso.chartPull (chartPullLinComb o.P _ _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ₂ f o.A) (fun _ => ?_))
      (chartPullLinComb o.P _ _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ₂ f o.A) (fun _ => ?_)) (o.rosati c)
    · refine lift_pφ₂ f _ _ _ _ _ ?_ (PullbackComparison.pφ₂_snd f o.A).symm
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← PullbackComparison.pφ₂_fst, Category.assoc]
    · refine lift_pφ₂ f _ _ _ _ _ (PullbackComparison.pφ₂_fst f o.A).symm ?_
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← PullbackComparison.pφ₂_snd, Category.assoc]
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  refine ⟨{ A := (Over.pullback f).obj o.A
            ab := hab
            act := OActN.pull f o.act
            P := o.P.pull (PullbackComparison.pφ₂ f o.A)
            isLB := hP
            rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
              (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
            rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
              (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
            symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
              (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ₂ f o.A) (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
            ample := hamp o.ample
            kerP := ?_
            rosati := hrose
            lie := ?_
            lieRank := fun k _ _ x β hx i =>
              (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A _ f _ (o.act.toF D) ((OActN.pull f o.act).toF D) h
                (fun c => hact _) k x (β.comp (b.t i)) D.m).2
                (o.lieRank k (x ≫ f) β ((Category.assoc _ _ _).trans hx) i)
            eta := fun y => GlobalTheory.ObjPull.secPull h (o.eta y)
            eta_add := fun y z => by rw [o.eta_add, map_mul]
            eta_lin := fun c y => by rw [o.eta_lin]; exact secPull_comp f h _ _ (hact c) _
            eta_ker := fun y => by rw [o.eta_ker y, map_one]
            geom := fun k _ _ x β hx => ?_ },
    ⟨{ φ := PullbackComparison.pφ f o.A
       φ₂ := PullbackComparison.pφ₂ f o.A
       cart := h
       sq := PullbackComparison.isSquare f o.A
       act := hact
       pol := PullbackComparison.gen_refl _ hP
       eta := fun y => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  · obtain ⟨e, he, hk⟩ := o.kerP
    refine ⟨e, he, fun T x H => ?_⟩
    have := hk (Over.mk (T.hom ≫ f)) (GlobalTheory.ObjPull.pushEquiv h T x) (gen_ker_push f o.P T x H)
    exact (GlobalTheory.ObjPull.pushEquiv h T).injective (by rw [map_pow, this, map_one])
  · intro R' _ β x hx v hv
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
      (Category.assoc _ _ _).symm
    obtain ⟨w₀, hw₀, hv₀⟩ := o.lie R' β (x ≫ f) ((Category.assoc _ _ _).trans hx) (e v)
      ((isTanScal_push f h o.act _ hact x e he _ _ v).1 hv)
    refine ⟨fun i => e.symm (w₀ i), fun i c => (isTanScal_push f h o.act _ hact x e he _ _ _).2
      (by rw [e.apply_symm_apply]; exact hw₀ i c), e.injective ?_⟩
    rw [hv₀, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  · obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β ((Category.assoc _ _ _).trans hx)
    refine ⟨tateMoveO (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' z hz => ?_) I, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A _ f _ _ _ hL hL' h hLi
        (Over.mk x) n g g' _ _ _ rfl rfl).2 hz
    · exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI y))

end GlobalTheory.UPel.HT.BaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  first | (exact @GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (exact GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (intros; apply GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionAdelicFromArchimedeanStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_solution_adelic_from_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E, (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) → ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  first | exact @GlobalTheory.normEq_inf_place | exact GlobalTheory.normEq_inf_place | (intros; apply GlobalTheory.normEq_inf_place <;> assumption)
end

