module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSub
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalProperty
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSubStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_mem_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ) (c : Acris l), Lat.pk l k (ACris.iota ℂ_[l] l c) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCris.cris_in | exact GlobalTheory.CompanionTheory.LatCris.cris_in | (intros; apply GlobalTheory.CompanionTheory.LatCris.cris_in <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
section
noncomputable section

open Finset Matrix MeasureTheory

namespace GlobalTheory.CompanionTheory.ActEquivK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma jm_inv (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε :=
  Matrix.inv_eq_left_inv (signature_matrix_sq ε)

lemma hinvol (ε : Fin n → Bool) : AAInvW.HInvol (Formalism.REAL.Jm ε) := by
  refine ⟨?_, signature_matrix_sq ε⟩
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

lemma eabH_eq (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Formalism.QuantumDeterminants.EabH (Formalism.REAL.Jm ε) a b f = Formalism.REAL.Eab ε a b f := by
  funext g
  have h1 : Formalism.QuantumDeterminants.hpart1 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart1 ε (Matrix.single a b 1) := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.REAL.cpart1
    rw [jm_inv]
  have h2 : Formalism.QuantumDeterminants.hpart2 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart2 ε (Matrix.single a b 1) := by
    unfold Formalism.QuantumDeterminants.hpart2 Formalism.REAL.cpart2
    rw [jm_inv]
  unfold Formalism.QuantumDeterminants.EabH
  rw [h1, h2]
  rfl

lemma inUJ_inv {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) : Formalism.REAL.inUJ ε k⁻¹ := by
  have hm : k * k⁻¹ = 1 := AAInvW.ana_mul_inv (hinvol ε) hk
  have h0 : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε := hk
  show (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = Formalism.REAL.Jm ε
  calc (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = (k⁻¹)ᴴ * (kᴴ * Formalism.REAL.Jm ε * k) * k⁻¹ := by rw [h0]
    _ = (k * k⁻¹)ᴴ * Formalism.REAL.Jm ε * (k * k⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hm]; simp

lemma smooth_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) :
    Formalism.REAL.SmoothOnG ε (fun x => f (x * k)) :=
  AAInvW.smooth_right' n (Formalism.REAL.Jm ε) ℂ f k (hinvol ε) hk hf

lemma eab_local {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n)
    (h : ∀ x, Formalism.REAL.inUJ ε x → f x = f' x) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eab ε a b f g = Formalism.REAL.Eab ε a b f' g := by
  rw [← eabH_eq, ← eabH_eq]
  exact AAInvW.eab_h_local n (Formalism.REAL.Jm ε) ℂ f f' a b g (hinvol ε) h hg

lemma eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Eab ε a b (fun _ => (0 : ℂ)) g = 0 := by
  simp [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]

lemma eab_lin {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (a b : Fin n)
    (hf : Formalism.REAL.SmoothOnG ε f) (hf' : Formalism.REAL.SmoothOnG ε f')
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => f x + c * f' x) g =
      Formalism.REAL.Eab ε a b f g + c * Formalism.REAL.Eab ε a b f' g := by
  have := AAInvW.eab_h_linear n (Formalism.REAL.Jm ε) ℂ f f' c a b g (hinvol ε) hf hf' hg
  simpa only [eabH_eq, smul_eq_mul] using this

lemma smooth_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) :
    Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, c i * F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.REAL.smooth_on_group_const_fun (ε := ε) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact Formalism.REAL.smooth_on_group_add (Formalism.REAL.smooth_on_group_const_mul (c i) (hF i)) ih

lemma eab_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eab ε a b (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using eab_zero (ε := ε) a b g
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have e : (fun x => c i * F i x + ∑ j ∈ s, c j * F j x) =
        fun x => (∑ j ∈ s, c j * F j x) + c i * F i x := funext fun x => add_comm _ _
    rw [e, eab_lin (c i) a b (smooth_sum s c F hF) (hF i) hg, ih, add_comm]

lemma eab_mul_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f) (a b : Fin n)
    {k g : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b f (g * k) =
      ∑ q : Fin n × Fin n, adC k (a, b) q * Formalism.REAL.Eab ε q.1 q.2 (fun x => f (x * k)) g := by
  have hJ := hinvol ε
  have hmi : k * k⁻¹ = 1 := AAInvW.ana_mul_inv hJ hk
  have him : k⁻¹ * k = 1 := AAInvW.ana_inv_mul hJ hk
  have hgk : Formalism.REAL.inUJ ε (g * k) := AAInvW.ana_mul hg hk
  have h := AAInvW.eab_h_right n (Formalism.REAL.Jm ε) ℂ (fun x => f (x * k)) a b k⁻¹ (g * k) hJ
    (smooth_right hf hk) (inUJ_inv hk) hgk
  have e1 : (fun x => (fun y => f (y * k)) (x * k⁻¹)) = f := by
    funext x
    show f (x * k⁻¹ * k) = f x
    rw [Matrix.mul_assoc, him, Matrix.mul_one]
  have e2 : g * k * k⁻¹ = g := by rw [Matrix.mul_assoc, hmi, Matrix.mul_one]
  have e3 : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv hmi
  rw [e1, e2, e3, eabH_eq] at h
  rw [h, Fintype.sum_prod_type]
  simp only [eabH_eq, smul_eq_mul]
  rfl

lemma eword_local (w : List (Fin n × Fin n)) {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ x, Formalism.REAL.inUJ ε x → f x = f' x) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eword ε w f g = Formalism.REAL.Eword ε w f' g := by
  induction w generalizing g with
  | nil => exact h g hg
  | cons p w ih => exact eab_local p.1 p.2 (fun x hx => ih hx) hg

lemma eword_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) (w : List (Fin n × Fin n))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eword ε w (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) g := by
  induction w generalizing g with
  | nil => rfl
  | cons p w ih =>
    show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w _) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w (F i)) g
    rw [eab_local p.1 p.2 (f' := fun x => ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) x)
      (fun x hx => ih hx) hg]
    exact eab_sum s c _ (fun i => Formalism.REAL.smooth_iterated_lie_derivative (hF i) w) p.1 p.2 hg

lemma sum_cons {α : Type*} [Fintype α] [DecidableEq α] {l : ℕ} (Φ : (Fin (l + 1) → α) → ℂ) :
    ∑ W, Φ W = ∑ q : α, ∑ w : Fin l → α, Φ (Fin.cons q w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

lemma eword_mul_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) :
    ∀ (l : ℕ) (x : Fin l → Fin n × Fin n) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε (List.ofFn x) f (g * k) =
        ∑ w : Fin l → Fin n × Fin n, (∏ i, adC k (x i) (w i)) *
          Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) g := by
  intro l
  induction l with
  | zero =>
    intro x g hg
    simp [Formalism.REAL.Eword]
  | succ l ih =>
    intro x g hg
    have hfk := smooth_right hf hk
    rw [sum_cons, List.ofFn_succ]
    show Formalism.REAL.Eab ε (x 0).1 (x 0).2 (Formalism.REAL.Eword ε (List.ofFn fun i => x i.succ) f) (g * k) = _
    rw [eab_mul_right (Formalism.REAL.smooth_iterated_lie_derivative hf _) _ _ hk hg]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [eab_local q.1 q.2 (f' := fun y => ∑ w : Fin l → Fin n × Fin n,
        (∏ i, adC k (x i.succ) (w i)) * Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) y)
      (fun y hy => ih _ y hy) hg,
      eab_sum _ _ _ (fun w => Formalism.REAL.smooth_iterated_lie_derivative hfk _) q.1 q.2 hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.prod_univ_succ, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    show _ = _ * Formalism.REAL.Eab ε q.1 q.2 (Formalism.REAL.Eword ε (List.ofFn w) _) g
    ring

theorem actEquiv : ActEquiv := by
  intro n ε lam T Ψ m hP k a
  have hk : Formalism.REAL.inUJ ε (toMK k) := (mir_inUJ_iff ε _).2 k.1.2
  have hJ : ∀ v, Formalism.REAL.SmoothOnG ε (jfun Ψ T.w v) := fun v =>
    pdA_smooth_clm (pdA_coef T.w v) (f := Ψ) hP.2.2.1
  have hJk : ∀ v y, Formalism.REAL.inUJ ε y →
      jfun Ψ T.w v (y * toMK k) = jfun Ψ T.w (T.op k v) y := by
    intro v y hy
    show inner ℂ T.w (Ψ (y * toMK k) v) = inner ℂ T.w (Ψ y (T.op k v))
    have h1 := hP.1 1 k y ((mir_inUJ_iff ε _).1 hy)
    rw [pdA_toMK_one, Matrix.one_mul, pdA_op_one, one_mul] at h1
    rw [h1]
    rfl
  unfold actL
  rw [rightRegular_toL2 ε _ (show toMK k ∈ UJset ε from k.1.2)]
  refine toL2_congr_of_forall_inUJ_eq fun g hg' => ?_
  have hg : Formalism.REAL.inUJ ε g := (mir_inUJ_iff ε _).2 hg'
  have hL : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (fun y => inner ℂ T.w (Ψ y (a x))) (g * toMK k) =
      ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (x.2 i) (w i)) *
        Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a x))) g := by
    intro x
    refine (eword_mul_right (hJ (a x)) hk x.1 x.2 g hg).trans (Finset.sum_congr rfl fun w _ => ?_)
    rw [eword_local (List.ofFn w) (f' := jfun Ψ T.w (T.op k (a x))) (fun y hy => hJk _ y hy) hg]
  have hR : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x)
        (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) g =
      ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (w i) (x.2 i)) *
        Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (T.op k (a ⟨x.1, w⟩))) g := by
    intro x
    have e : (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) = fun y =>
        ∑ w ∈ (Finset.univ : Finset (Fin x.1 → Fin n × Fin n)), (∏ i, adC (toMK k) (w i) (x.2 i)) *
          jfun Ψ T.w (T.op k (a ⟨x.1, w⟩)) y := by
      funext y
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rhoA, map_sum, map_smul, inner_sum, inner_smul_right, jfun]
    rw [e]
    exact eword_sum _ _ _ (fun w => hJ _) _ hg
  show actF T Ψ a (g * toMK k) = actF T Ψ (rhoA T m k a) g
  unfold actF
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [hL, hR]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.sum_comm (s := (Finset.univ : Finset (Fin (l : ℕ) → Fin n × Fin n))) (t := Finset.univ)
    (f := fun y w => (∏ i, adC (toMK k) (y i) (w i)) *
      Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a ⟨l, y⟩))) g)

end GlobalTheory.CompanionTheory.ActEquivK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.AdmFL

variable {G X Y Z : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z]

theorem mem_fixed_iff {α : Representation ℂ G X} {K : Subgroup G} {x : X} :
    x ∈ fixed α K ↔ ∀ g ∈ K, α g x = x := by
  change (∀ h : K, α h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

private theorem finiteDimensional_fixed_of_exact_lemma {α : Representation ℂ G X}
    {β : Representation ℂ G Y} (i : α.IntertwiningMap β) (g : G) (x : X) :
    i (α g x) = β g (i x) := by
  have h := LinearMap.congr_fun (i.isIntertwining' g) x
  simpa [LinearMap.comp_apply] using h

theorem finiteDimensional_fixed_of_exact {α : Representation ℂ G X} {β : Representation ℂ G Y}
    {γ : Representation ℂ G Z} (i : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hi : Function.Injective i) (hker : ∀ y, p y = 0 → ∃ x, i x = y) (K : Subgroup G)
    [FiniteDimensional ℂ (fixed α K)] [FiniteDimensional ℂ (fixed γ K)] :
    FiniteDimensional ℂ (fixed β K) := by
  let j : fixed α K →ₗ[ℂ] fixed β K :=
    { toFun := fun x => ⟨i x, mem_fixed_iff.2 fun g hg => by
        rw [← finiteDimensional_fixed_of_exact_lemma i g x, mem_fixed_iff.1 x.2 g hg]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let q : fixed β K →ₗ[ℂ] fixed γ K :=
    { toFun := fun y => ⟨p y, mem_fixed_iff.2 fun g hg => by
        rw [← finiteDimensional_fixed_of_exact_lemma p g y, mem_fixed_iff.1 y.2 g hg]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hK : LinearMap.ker q ≤ LinearMap.range j := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hpy : p (y : Y) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := hker _ hpy
    have hxfix : x ∈ fixed α K := mem_fixed_iff.2 fun g hg => hi (by
      rw [finiteDimensional_fixed_of_exact_lemma i, hx, mem_fixed_iff.1 y.2 g hg])
    exact ⟨⟨x, hxfix⟩, Subtype.ext hx⟩
  refine ⟨?_⟩
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (f := q)
  · exact IsNoetherian.noetherian _
  · rw [Submodule.fg_iff_finiteDimensional]
    exact Submodule.finiteDimensional_of_le (le_trans inf_le_right hK)

private theorem isAdmissible_of_hasFiniteLength_lemma_3 {M : Type} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (g : G) (x : M) :
    Representation.ofModule' (k := ℂ) (G := G) M g x = MonoidAlgebra.single g (1 : ℂ) • x := by
  first
  | rfl
  | simp only [Representation.ofModule', MonoidAlgebra.lift_symm_apply, Algebra.lsmul_coe]

private theorem isAdmissible_of_hasFiniteLength_lemma_2 {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [Module (MonoidAlgebra ℂ G) M₁] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [Module (MonoidAlgebra ℂ G) M₂] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M₂]
    (f : M₁ →ₗ[MonoidAlgebra ℂ G] M₂) :
    ∃ φ : (Representation.ofModule' (k := ℂ) (G := G) M₁).IntertwiningMap
        (Representation.ofModule' (k := ℂ) (G := G) M₂), ∀ x, φ x = f x := by
  refine ⟨⟨f.restrictScalars ℂ, fun g => ?_⟩, fun x => rfl⟩
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, isAdmissible_of_hasFiniteLength_lemma_3,
    map_smul]

private theorem isAdmissible_of_hasFiniteLength_lemma_5 {M : Type} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [IsSimpleModule (MonoidAlgebra ℂ G) M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible := by
  have e : Subrepresentation (Representation.ofModule' (k := ℂ) (G := G) M) ≃o
      Submodule (MonoidAlgebra ℂ G) M :=
    { toFun := fun S =>
        { carrier := S.toSubmodule
          add_mem' := fun hx hy => S.toSubmodule.add_mem hx hy
          zero_mem' := S.toSubmodule.zero_mem
          smul_mem' := fun a x hx => by
            induction a using MonoidAlgebra.induction_on with
            | of g =>
              rw [MonoidAlgebra.of_apply, ← isAdmissible_of_hasFiniteLength_lemma_3]
              exact S.apply_mem_toSubmodule g hx
            | add a b ha hb =>
              rw [add_smul]
              exact S.toSubmodule.add_mem ha hb
            | smul r a ha =>
              rw [smul_assoc]
              exact S.toSubmodule.smul_mem r ha }
      invFun := fun P => ⟨P.restrictScalars ℂ, fun g v hv => by
        rw [Submodule.restrictScalars_mem, isAdmissible_of_hasFiniteLength_lemma_3]
        exact P.smul_mem _ hv⟩
      left_inv := fun S => by
        apply Subrepresentation.ext
        rfl
      right_inv := fun P => by
        ext x
        rfl
      map_rel_iff' := by
        intro S T
        exact Iff.rfl }
  exact e.isSimpleOrder

private theorem isAdmissible_of_hasFiniteLength_lemma_4 [TopologicalSpace G] (K : Subgroup G) :
    ∀ {M : Type} [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M], IsFiniteLength (MonoidAlgebra ℂ G) M →
    ∀ [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
      IsSubquotient σ (Representation.ofModule' (k := ℂ) (G := G) M) → σ.IsIrreducible → IsAdmissible σ) →
    IsOpen (K : Set G) → IsCompact (K : Set G) →
    FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) M) K) := by
  intro M _ _ hM
  induction hM with
  | of_subsingleton =>
    intro _ _ _ _ _
    infer_instance
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro _ _ hsub hKo hKc
    obtain ⟨i, hi⟩ := isAdmissible_of_hasFiniteLength_lemma_2 (G := G) N.subtype
    obtain ⟨p, hp⟩ := isAdmissible_of_hasFiniteLength_lemma_2 (G := G) N.mkQ
    have hinj : Function.Injective i := by
      intro x y hxy
      rw [hi, hi] at hxy
      exact Subtype.ext hxy
    have hker : ∀ y, p y = 0 → ∃ x, i x = y := by
      intro y hy
      rw [hp, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact ⟨⟨y, hy⟩, by rw [hi]; rfl⟩
    have hsurj : Function.Surjective p := by
      intro z
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective N z
      exact ⟨m, by rw [hp]; exact hm⟩
    have hNsub : IsSubquotient (Representation.ofModule' (k := ℂ) (G := G) N)
        (Representation.ofModule' (k := ℂ) (G := G) M) := IsSubquotient.of_injective i hinj
    haveI : FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) N) K) :=
      ih (fun W _ _ σ hσ hirr => hsub W σ (hσ.trans hNsub) hirr) hKo hKc
    haveI : FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) (M ⧸ N)) K) := by
      have hirr : (Representation.ofModule' (k := ℂ) (G := G) (M ⧸ N)).IsIrreducible :=
        isAdmissible_of_hasFiniteLength_lemma_5
      have hadm := hsub _ _ (IsSubquotient.of_surjective p hsurj) hirr
      unfold IsAdmissible at hadm
      exact hadm.2 K hKo hKc
    exact finiteDimensional_fixed_of_exact i p hinj hker K

theorem isAdmissible_of_hasFiniteLength : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), IsSubquotient σ ρ → σ.IsIrreducible → IsAdmissible σ) → IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ hsm hfl hirr
  unfold IsAdmissible
  refine ⟨hsm, fun K hKo hKc => ?_⟩
  letI instA : Module (MonoidAlgebra ℂ G) V := Module.compHom V ρ.asAlgebraHom.toRingHom
  haveI instT : IsScalarTower ℂ (MonoidAlgebra ℂ G) V := ⟨fun c a v => by
    show ρ.asAlgebraHom (c • a) v = c • ρ.asAlgebraHom a v
    rw [map_smul]
    rfl⟩
  have hρ : Representation.ofModule' (k := ℂ) (G := G) V = ρ := by
    ext g v
    rw [isAdmissible_of_hasFiniteLength_lemma_3]
    show ρ.asAlgebraHom (MonoidAlgebra.single g 1) v = ρ g v
    rw [Representation.asAlgebraHom_single_one]
  have hfl' : IsFiniteLength (MonoidAlgebra ℂ G) V := hfl
  have h := @isAdmissible_of_hasFiniteLength_lemma_4 G _ _ K V _ instA hfl' _ instT
    (fun W _ _ σ hσ h => hirr W σ (hρ ▸ hσ) h) hKo hKc
  rw [hρ] at h
  exact h

end GlobalTheory.CompanionTheory.AdmFL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystemStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_rees_closed_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent → ∀ c : ℕ, (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) → ∃ c' : ℕ, ClosedSys I (D : X.Modules) (restrictSys I D S c') ∧ PropSupp A (restrictSys I D S c' 0) ∧ (Alg I (D : X.Modules) (restrictSys I D S c') → PropSupp A D → Alg I E S) := by
  exact @GlobalTheory.CompanionTheory.GE.Comb.restrict_alg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalPropertyStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_algebra_universal_property : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : (((base l).cont ℤ_[l]).A)ˣ, ((base l).cont ℤ_[l]).sharp η = 1 ∧ PAlg.Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η ∧ ∀ (A t : PAlg l), t.IsTest → ∀ (φ : A ⟶ t) (u : (t.A)ˣ), t.sharp u = 1 → ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) η) = u := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.main | exact GlobalTheory.CompanionTheory.ContUniv.main | (intros; apply GlobalTheory.CompanionTheory.ContUniv.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableSubgroupClosure
section
open MeasureTheory Filter Topology
open scoped ENNReal
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LatCount

theorem countable_subgroupClosure {G : Type*} [Group G] (s : Set G) (hs : s.Countable) :
    ((Subgroup.closure s : Subgroup G) : Set G).Countable := by
  open scoped Pointwise in
  have ht : (s ∪ s⁻¹).Countable := hs.union (by simpa using hs.image (·⁻¹))
  haveI : Countable ↥(s ∪ s⁻¹) := ht.to_subtype
  have h : ((Subgroup.closure s : Subgroup G) : Set G)
      = Set.range (FreeMonoid.lift ((↑) : ↥(s ∪ s⁻¹) → G)) := by
    have h1 : ((Subgroup.closure s : Subgroup G) : Set G)
        = ((Submonoid.closure (s ∪ s⁻¹) : Submonoid G) : Set G) := by
      rw [← Subgroup.closure_toSubmonoid]; rfl
    rw [h1, Submonoid.closure_eq_mrange]; rfl
  rw [h]
  exact Set.countable_range _

theorem countable_lat (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Countable (PositivityTheory.Rg.Rs.An.lat K n) := by
  haveI : Countable K := GroundTheory.Global.countable_numberField K
  haveI : Countable (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (Countable (Fin n → Fin n → K))
  haveI : Countable (GL (Fin n) K) := Units.val_injective.countable
  have h1 : (Set.range (AdelicGLn.diagonal K n)).Countable := Set.countable_range _
  have h2 : ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)).Countable := by
    rw [Subgroup.coe_zpowers]
    exact Set.countable_range _
  have h3 := countable_subgroupClosure
    ((Set.range (AdelicGLn.diagonal K n)) ∪
      ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) (h1.union h2)
  have h4 : PositivityTheory.Rg.Rs.An.lat K n = Subgroup.closure
      ((Set.range (AdelicGLn.diagonal K n)) ∪
        ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
        Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) := by
    unfold PositivityTheory.Rg.Rs.An.lat
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [h4]
  exact h3.to_subtype

end GlobalTheory.CompanionTheory.LatCount
end

