module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0171
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedTwoCharactersNotScalar
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SplitFrob

section Proj

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isCompl_toSubmodule {S S' : Subrepresentation π} (h : IsCompl S S') :
    IsCompl S.toSubmodule S'.toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, disjoint_iff.mp h.1]
    try rfl
  · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, codisjoint_iff.mp h.2]
    try rfl

def proj {S S' : Subrepresentation π} (h : IsCompl S S') : V →ₗ[ℂ] V :=
  S.toSubmodule.subtype ∘ₗ
    Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h)

theorem proj_left {S S' : Subrepresentation π} (h : IsCompl S S') {v : V} (hv : v ∈ S.toSubmodule) :
    proj h v = v := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = v
  simp only [Submodule.projectionOnto_apply_of_mem_left _ hv, Submodule.subtype_apply]

theorem proj_right {S S' : Subrepresentation π} (h : IsCompl S S') {v : V}
    (hv : v ∈ S'.toSubmodule) : proj h v = 0 := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = 0
  simp only [Submodule.projectionOnto_apply_of_mem_right _ hv, map_zero]

theorem proj_comm {S S' : Subrepresentation π} (h : IsCompl S S') (g : G) (v : V) :
    proj h (π g v) = π g (proj h v) := by
  have htop : S.toSubmodule ⊔ S'.toSubmodule = ⊤ := (isCompl_toSubmodule h).sup_eq_top
  have hv : v ∈ S.toSubmodule ⊔ S'.toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [map_add (f := _), proj_left h hx, proj_right h hy, proj_left h (S.apply_mem_toSubmodule g hx),
    proj_right h (S'.apply_mem_toSubmodule g hy), add_zero]

end Proj

section Induced

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {X : Type} [AddCommGroup X] [Module ℂ X]

def ev (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) : IndSp e ρ →ₗ[ℂ] X where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_unip (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {u : GL n k}
    (hu : u ∈ unipRad k e) (f : IndSp e ρ) : ev e ρ (parInd e ρ u f) = ev e ρ f := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hu
  rw [MonoidHom.mem_ker] at hp
  have h := f.1.2 p 1
  rw [MonoidHom.comp_apply, hp, map_one, Module.End.one_apply, mul_one] at h
  show f.1.1 (1 * ((parab k e).subtype p)) = f.1.1 1
  rw [one_mul]
  exact h

theorem ev_levi (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) (g : Levi k m)
    (f : IndSp e ρ) :
    ev e ρ (parInd e ρ (leviEmb k e g) f) = (deltaHalf k m g : ℂ) • ρ g (ev e ρ f) := by
  have hmem := leviEmb_mem_parab k e g
  have h := f.1.2 ⟨leviEmb k e g, hmem⟩ 1
  rw [mul_one, MonoidHom.comp_apply, leviProj_leviEmb] at h
  show f.1.1 (1 * leviEmb k e g) = (deltaHalf k m g : ℂ) • ρ g (f.1.1 1)
  rw [one_mul]
  exact h

theorem exists_ev_ne (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {f : IndSp e ρ}
    (hf : f ≠ 0) : ∃ g, ev e ρ (parInd e ρ g f) ≠ 0 := by
  by_contra hcon
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  funext g
  by_contra hg
  exact hcon ⟨g, by
    change f.1.1 (1 * g) ≠ 0
    rw [one_mul]
    exact hg⟩

variable {e : (Σ a, m a) ≃ n} {ρ : Representation ℂ (Levi k m) X}

def lam {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') : IndSp e ρ →ₗ[ℂ] X :=
  ev e ρ ∘ₗ proj h

theorem lam_apply {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (f : IndSp e ρ) :
    lam h f = ev e ρ (proj h f) := rfl

theorem lam_twKer {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    twKer (parInd e ρ) (unipRad k e) 1 ≤ LinearMap.ker (lam h) := by
  unfold GlobalTheory.PRep.twKer
  refine Submodule.span_le.mpr ?_
  rintro w ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul,
    lam_apply, lam_apply, proj_comm, ev_unip e ρ u.2, sub_self]

def frob {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    (jac e (parInd e ρ)).IntertwiningMap ρ where
  toLinearMap := (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
  isIntertwining' g := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
        (jac e (parInd e ρ) g (Submodule.Quotient.mk v)) = ρ g (lam h v)
    rw [jac_mk, ← Submodule.Quotient.mk_smul, Submodule.liftQ_apply, map_smul, lam_apply, proj_comm,
      ev_levi, lam_apply, smul_smul]
    simp

theorem frob_mk {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (v : IndSp e ρ) :
    (frob h).toLinearMap (Submodule.Quotient.mk v) = lam h v := rfl

theorem exists_lam_ne {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥) :
    ∃ v ∈ S.toSubmodule, lam h v ≠ 0 := by
  have hS0 : S.toSubmodule ≠ ⊥ := by
    intro h0
    apply hS
    apply Subrepresentation.ext
    rw [h0]
    try rfl
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨g, hg⟩ := exists_ev_ne e ρ hf0
  refine ⟨parInd e ρ g f, S.apply_mem_toSubmodule g hfS, ?_⟩
  rw [lam_apply, proj_left h (S.apply_mem_toSubmodule g hfS)]
  exact hg

theorem not_dichotomy {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥)
    (hS' : S' ≠ ⊥) :
    ¬ (∀ φ ψ : (jac e (parInd e ρ)).IntertwiningMap ρ,
      φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro hd
  obtain ⟨v, hvS, hv⟩ := exists_lam_ne h hS
  obtain ⟨w, hwS', hw⟩ := exists_lam_ne h.symm hS'
  rcases hd (frob h) (frob h.symm) with h0 | ⟨c, hc⟩
  · apply hv
    rw [← frob_mk h v, h0, LinearMap.zero_apply]
  · have e1 : lam h.symm v = c • lam h v := by
      rw [← frob_mk h.symm v, hc, LinearMap.smul_apply, frob_mk]
    rw [lam_apply, proj_right h.symm hvS, map_zero] at e1
    rcases smul_eq_zero.mp e1.symm with hc0 | hc0
    · apply hw
      rw [← frob_mk h.symm w, hc, hc0, zero_smul, LinearMap.zero_apply]
    · exact hv hc0

end Induced

theorem not_dichotomy_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (W W' : Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))), IsCompl W W' → W ≠ ⊥ → W' ≠ ⊥ → ¬ (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ W W' h hW hW'
  exact not_dichotomy h hW hW'

end GlobalTheory.CompanionTheory.SplitFrob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitarisableDegenerateSeries
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenerateSeries

theorem isUnitarisable_degenerateSeries (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (_ : IsSmoothChar χ₁)
    (_ : IsSmoothChar χ₂) (h₁ : IsUnitaryChar χ₁) (h₂ : IsUnitaryChar χ₂) :
    IsUnitarisable (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  apply GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₁ _
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₂ _

end GlobalTheory.CompanionTheory.DegenerateSeries
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct ValuativeRel

namespace GlobalTheory.CompanionTheory.IwahoriDatumGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

theorem fact_up' {x : GL (Fin n) k} (hx : x ∈ iwahori k (Fin n)) :
    ∃ c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n), ∃ b ∈ iwahori k (Fin n) ⊓ (diagT k (Fin n)).range,
      ∃ a ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n), x = c * b * a := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hx
  exact ⟨u, ⟨(GlobalTheory.IwahoriTraceProof.mem_unipO_iff hu.1).2 hu, hu.1⟩, _,
    ⟨diagT_mem_iwahori hd, ⟨d, rfl⟩⟩, c, ⟨KOne_le_iwahori k (Fin n) hc.2, hc.1⟩, rfl⟩

end GlobalTheory.CompanionTheory.IwahoriDatumGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentIdentityMorphismCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcCov

theorem tens_transport {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    {A B : Type 1} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {S : Type} [CommRing S] {A' B' : Type 1} [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B']
    (f : Unit → N → A → A') (f' : Unit → N → B → B') (e : B →ₗ[R] A) (he : Function.Bijective e)
    (e' : B' →ₗ[S] A') (he' : Function.Bijective e') (comm : ∀ i n x, e' (f' i n x) = f i n (e x))
    (H : Tens R (N := fun _ : Unit => N) (M := fun _ => A) (M' := A') f) :
    Tens R (N := fun _ : Unit => N) (M := fun _ => B) (M' := B') f' := by
  obtain ⟨g, hg⟩ := H
  let E : B ≃ₗ[R] A := LinearEquiv.ofBijective e he
  let TE : N ⊗[R] B ≃ₗ[R] N ⊗[R] A := TensorProduct.congr (LinearEquiv.refl R N) E
  let P : (∀ _ : Unit, N ⊗[R] B) ≃+ (∀ _ : Unit, N ⊗[R] A) := AddEquiv.piCongrRight fun _ => TE.toAddEquiv
  let E' : B' ≃+ A' := (LinearEquiv.ofBijective e' he').toAddEquiv
  refine ⟨(P.trans g).trans E'.symm, fun i n x => ?_⟩
  apply E'.injective
  have hP : P (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ e x) := by
    funext k
    obtain rfl : k = i := Subsingleton.elim _ _
    simp [P, TE, E]
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hP, hg]
  exact (comm i n x).symm

section
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem pt_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (T : Thick (nlFun γ' p X q κ')) :
    pt ((m.mor p).functor.obj T) = pt T ≫ m.u := rfl

theorem inU_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (V : X.Opens)
    (T : Thick (nlFun γ' p X q κ')) (h : InU V T) : InU V ((m.mor p).functor.obj T) := by
  unfold InU at h ⊢
  rw [pt_obj, hu, Category.comp_id]
  exact h

def tmor (m : NMor γ q κ γ' q κ' (algebraMap R R')) (p : ℕ) :
    SMor (thP (nlFun γ p X q κ)) (thP (nlFun γ' p X q κ')) (algebraMap R R') where
  G := (m.mor p).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

end

abbrev aT {b : Base} (L : b.Fun) : IdF (thA L) := (thFil L 0).sup (IdF.span _ 0)

abbrev aB {b : Base} (L : b.Fun) : IdF (thA L) := (IdF.bot _).sup (IdF.span _ 0)

theorem aT_top {b : Base} (L : b.Fun) (T : Thick L) : (aT L).S T = ⊤ := by
  have h : (thFil L 0).S T = ⊤ := T.pdPow_zero
  exact top_le_iff.1 (h ▸ le_sup_left)

theorem aB_bot {b : Base} (L : b.Fun) (T : Thick L) : (aB L).S T = ⊥ := by
  change (⊥ : Ideal _) ⊔ Ideal.span {algebraMap b.R _ 0} = ⊥
  simp

theorem mapH_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K L : Cx.{1} R} {L' P : Cx.{1} R'}
    (φ : Cx.Hom K L' σ) (ψ : Cx.Hom L' P (RingHom.id R')) (φ' : Cx.Hom K L (RingHom.id R)) (ψ' : Cx.Hom L P σ) (n : ℕ)
    (h : ∀ z, ψ.f n (φ.f n z) = ψ'.f n (φ'.f n z)) (c : K.H n) : ψ.mapH n (φ.mapH n c) = ψ'.mapH n (φ'.mapH n c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (h z.1))

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem leC_top (f : SMor Φ Φ' σ) (c : R') (a : IdF Φ.A) (a' : IdF Φ'.A) (h : ∀ T, a'.S T = ⊤) : f.LeC c a a' :=
  fun T _ _ => by rw [h]; trivial

theorem leC_bot (f : SMor Φ Φ' σ) (c : R') (b : IdF Φ.A) (b' : IdF Φ'.A) (h : ∀ T, b.S (f.G.obj T) = ⊥) : f.LeC c b b' := by
  intro T x hx
  rw [h, Ideal.mem_bot] at hx
  subst hx
  rw [map_zero, mul_zero]
  exact Ideal.zero_mem _

theorem sqC_add (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (c c' : R') (ha : f.LeC c a a') (hb : f.LeC c b b')
    (ha' : f.LeC c' a a') (hb' : f.LeC c' b b') (ha'' : f.LeC (c + c') a a') (hb'' : f.LeC (c + c') b b') (T : C')
    (x : (sq a b).obj (f.G.obj T)) :
    (f.sqC (c + c') ha'' hb'').τ T x = (f.sqC c ha hb).τ T x + (f.sqC c' ha' hb').τ T x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * f.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * f.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * f.ρ T y)
  rw [map_add (f := _), add_mul, map_add (f := _)]

theorem sq_val (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : f.Le a a') (hb : f.Le b b') (T : C')
    (v : sqM a b (f.G.obj T)) :
    (show sqM a' b' T from (f.sq ha hb).τ T v).1 = Ideal.quotientMap (b'.S T) (f.ρ T) (fun y hy => hb T y hy) v.1 := rfl

theorem sqC_val (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (c : R') (ha : f.LeC c a a') (hb : f.LeC c b b') (T : C')
    (v : sqM a b (f.G.obj T)) : (show sqM a' b' T from (f.sqC c ha hb).τ T v).1 = f.qC c hb T v.1 := rfl

end Gen

theorem sqC_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (f : SMor Φ Φ' (algebraMap R R')) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (r : R) (c : R')
    (ha : f.LeC c a a') (hb : f.LeC c b b') (ha' : f.LeC (r • c) a a') (hb' : f.LeC (r • c) b b') (T : C')
    (x : (sq a b).obj (f.G.obj T)) :
    (f.sqC (r • c) ha' hb').τ T x = algebraMap R R' r • (f.sqC c ha hb).τ T x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (r • c) * f.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R R' r • (algebraMap R' _ c * f.ρ T y))
  refine congrArg (Ideal.Quotient.mk _) ?_
  rw [Algebra.smul_def r c, map_mul, mul_assoc, Algebra.smul_def (algebraMap R R' r)]

section Sq
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem st_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (𝒱 : Set X.Opens)
    (T : Thick (nlFun γ' p X q κ')) (h : St ⊤ 𝒱 T) : St ⊤ 𝒱 ((m.mor p).functor.obj T) := by
  obtain ⟨-, W, hW, hi⟩ := h
  exact ⟨trivial, W, hW, inU_obj m hu W T hi⟩

theorem square_tau (m : NMor γ q κ γ' q κ' (algebraMap R R')) {Q₁ Q₂ : ObjectProperty (Thick (nlFun γ p X q κ))}
    {Q₁' Q₂' : ObjectProperty (Thick (nlFun γ' p X q κ'))} (h : Q₂ ≤ Q₁) (h' : Q₂' ≤ Q₁')
    (k₁ : ∀ T, Q₁' T → Q₁ ((m.mor p).functor.obj T)) (k₂ : ∀ T, Q₂' T → Q₂ ((m.mor p).functor.obj T)) (a : R')
    (ha₁ : (m.smor Q₁ Q₁' k₁).LeC a (oT Q₁) (oT Q₁')) (hb₁ : (m.smor Q₁ Q₁' k₁).LeC a (oB Q₁) (oB Q₁'))
    (ha₂ : (m.smor Q₂ Q₂' k₂).LeC a (oT Q₂) (oT Q₂')) (hb₂ : (m.smor Q₂ Q₂' k₂).LeC a (oB Q₂) (oB Q₂'))
    (T : Q₂'.FullSubcategory) (w : (sq (oT Q₁) (oB Q₁)).obj ((m.smor Q₁ Q₁' k₁).G.obj ((incl h').G.obj T))) :
    ((incl h').sq (incl_std h' (some 0) 0) (incl_std h' none 0)).τ T (((m.smor Q₁ Q₁' k₁).sqC a ha₁ hb₁).τ _ w) =
      ((m.smor Q₂ Q₂' k₂).sqC a ha₂ hb₂).τ T (((incl h).sq (incl_std h (some 0) 0) (incl_std h none 0)).τ _ w) := by
  obtain ⟨w, hw⟩ := w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine Subtype.ext ?_
  refine (sq_val (incl h') _ _ T _).trans ?_
  refine Eq.trans ?_ (sqC_val (m.smor Q₂ Q₂' k₂) a ha₂ hb₂ T _).symm
  rw [sqC_val, sq_val]
  dsimp only
  refine (congrArg (Ideal.quotientMap _ _ _) (SMor.qC_mk (m.smor Q₁ Q₁' k₁) a hb₁ ((incl h').G.obj T) y)).trans ?_
  refine (Ideal.quotientMap_mk).trans ?_
  refine Eq.trans ?_ (congrArg ((m.smor Q₂ Q₂' k₂).qC a hb₂ T) Ideal.quotientMap_mk).symm
  refine Eq.trans ?_ (SMor.qC_mk (m.smor Q₂ Q₂' k₂) a hb₂ T _).symm
  rfl

theorem pull_square (m : NMor γ q κ γ' q κ' (algebraMap R R')) {Q₁ Q₂ : ObjectProperty (Thick (nlFun γ p X q κ))}
    {Q₁' Q₂' : ObjectProperty (Thick (nlFun γ' p X q κ'))} (h : Q₂ ≤ Q₁) (h' : Q₂' ≤ Q₁')
    (k₁ : ∀ T, Q₁' T → Q₁ ((m.mor p).functor.obj T)) (k₂ : ∀ T, Q₂' T → Q₂ ((m.mor p).functor.obj T)) (a : R')
    (ha₁ : (m.smor Q₁ Q₁' k₁).LeC a (oT Q₁) (oT Q₁')) (hb₁ : (m.smor Q₁ Q₁' k₁).LeC a (oB Q₁) (oB Q₁'))
    (ha₂ : (m.smor Q₂ Q₂' k₂).LeC a (oT Q₂) (oT Q₂')) (hb₂ : (m.smor Q₂ Q₂' k₂).LeC a (oB Q₂) (oB Q₂'))
    (j : ℕ) (x : CH.H (sq (oT Q₁) (oB Q₁)) j) :
    ((incl h').sq (incl_std h' (some 0) 0) (incl_std h' none 0)).pull j (((m.smor Q₁ Q₁' k₁).sqC a ha₁ hb₁).pull j x) =
      ((m.smor Q₂ Q₂' k₂).sqC a ha₂ hb₂).pull j (((incl h).sq (incl_std h (some 0) 0) (incl_std h none 0)).pull j x) :=
  mapH_square _ _ _ _ j (fun z => funext fun s => square_tau m h h' k₁ k₂ a ha₁ hb₁ ha₂ hb₂ _ _) x

end Sq

theorem bc_cover : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] {I : Ideal R}
    {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} (hp : p ≠ 0) (hn : IsNilpotent (p : R))
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}
    (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) (U : Cov q)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (hQ : Q = St ⊤ {⊤}) (hQ' : Q' = St ⊤ {⊤}) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    (ha : ∀ a : R', (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : ∀ a : R', (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ),
    Tens R (N := fun _ : Unit => R') (M := fun _ => CH.H (sq (oT Q) (oB Q)) j) (M' := CH.H (sq (oT Q') (oB Q')) j)
      fun _ a x => ((m.smor Q Q' h).sqC a (ha a) (hb a)).pull j x := by
  intro O R R' _ _ _ _ _ I I' γ γ' p hp hn X q κ κ' m hu hg U Q Q' hQ hQ' h ha hb j
  subst hQ hQ'
  have hA : ∀ a : R', (tmor m p).LeC a (aT _) (aT _) := fun a => leC_top _ a _ _ (aT_top _)
  have hB : ∀ a : R', (tmor m p).LeC a (aB _) (aB _) := fun a => leC_bot _ a _ _ fun T => aB_bot _ _
  have A : ∀ (𝒱 : Set X.Opens) (k : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ 𝒱 T → St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱 ((m.mor p).functor.obj T)) (a : R'),
      (m.smor _ _ k).LeC a (oT _) (oT _) := fun 𝒱 k a => leC_top _ a _ _ fun T => aT_top _ T.obj
  have B : ∀ (𝒱 : Set X.Opens) (k : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ 𝒱 T → St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱 ((m.mor p).functor.obj T)) (a : R'),
      (m.smor _ _ k).LeC a (oB _) (oB _) := fun 𝒱 k a => leC_bot _ a _ _ fun T => aB_bot _ _
  have Hg : Tens R (N := fun _ : Unit => R')
      (M := fun _ => CH.H (sq (oT (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U))) (oB (St ⊤ (Set.range U.U)))) j)
      (M' := CH.H (sq (oT (St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Set.range U.U))) (oB (St ⊤ (Set.range U.U)))) j)
      fun _ a x => ((m.smor _ _ (st_obj m hu _)).sqC a (A _ (st_obj m hu _) a) (B _ (st_obj m hu _) a)).pull j x := by
    refine GlobalTheory.T.stable_cover_cech_vanishing.2.2 (m.mor p).functor (fun _ : Unit => R') (fun _ => sq (aT _) (aB _)) (sq (aT _) (aB _))
      (fun _ a T => ((tmor m p).sqC a (hA a) (hB a)).τ T) (fun _ a _ _ φ x => ((tmor m p).sqC a (hA a) (hB a)).nat φ x)
      (fun _ a a' T x => sqC_add (tmor m p) a a' (hA a) (hB a) (hA a') (hB a') (hA _) (hB _) T x) (fun _ r a T x => sqC_smul (tmor m p) r a (hA a) (hB a) (hA _) (hB _) T x)
      ⊤ ⊤ U.U U.U (fun _ => st_obj m hu _) (fun _ => st_obj m hu _) (st_obj m hu _) ?_ j
    intro S hS j
    obtain ⟨α, hα⟩ := id hS
    obtain ⟨c', -⟩ := coord_res (U.c α) (iInf₂_le α hα) (U.inter S hS)
    exact GlobalTheory.CompanionTheory.ChartLocBc.local_bc hp hn m hu hg c' _ _ rfl rfl (st_obj m hu _) (A _ _) (B _ _) j
  have h₁ : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩
  have h₂ : St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup (Set.range U.U) := by
    rintro W rfl
    rw [sSup_range, U.cover]
  have b₁ := (zar (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) _ _ h₁ hc j).2.1 (some 0) none 0 0
  have b₂ := (zar (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) _ _ h₂ hc j).2.1 (some 0) none 0 0
  exact tens_transport _ _ _ b₁ _ b₂
    (fun _ a x => pull_square m h₁ h₂ h (st_obj m hu _) a (ha a) (hb a) (A _ _ a) (B _ _ a) j x) Hg

end GlobalTheory.CompanionTheory.BcCov
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuGaloisCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.MuGal

theorem mu_gal {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j) :
    B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) = Mid.mu r M n j hT (galM r M σ hσ n j t) := by
  unfold B.galHc Mid.mu galM B.galMorC Mid.muMor galT'
  symm
  exact cr_square
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl)
    (Mid.mIn r M n hT)
    (Mid.mIn r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl)
    (galBase_cris σ n) (fun _ => rfl) (fun _ => rfl) (galBase_cris σ n) (fun _ => rfl)
    (fun _ _ => rfl) j t

end GlobalTheory.CompanionTheory.MuGal
end
end

