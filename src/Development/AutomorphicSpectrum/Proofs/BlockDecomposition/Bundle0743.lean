module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonMapsBijectiveFinite
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfVB

section Pi

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

def piS {I : Type} {M N : I → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (u : ∀ i, M i →ₛₗ[algebraMap R S] N i) :
    (∀ i, M i) →ₛₗ[algebraMap R S] (∀ i, N i) where
  toFun x i := u i (x i)
  map_add' x y := funext fun i ↦ map_add (u i) _ _
  map_smul' r x := funext fun i ↦ (u i).map_smulₛₗ r (x i)

theorem liftSemi_piS_bijective {I : Type} [Finite I] {M N : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (u : ∀ i, M i →ₛₗ[algebraMap R S] N i) (hu : ∀ i, Function.Bijective (liftSemi (u i))) :
    Function.Bijective (liftSemi (piS u)) := by
  classical
  haveI := Fintype.ofFinite I
  let e := TensorProduct.piRight R S S M
  have key : (liftSemi (piS u) : S ⊗[R] (∀ i, M i) → ∀ i, N i) =
      (Pi.map fun i ↦ liftSemi (u i)) ∘ e := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero =>
      funext i
      simp
    | add a b ha hb =>
      simp only [map_add (f := _), Function.comp_apply] at ha hb ⊢
      rw [ha, hb]
      funext i
      simp
    | tmul s x =>
      funext i
      simp [e, liftSemi_tmul, piS]
  rw [key]
  exact (Function.Bijective.piMap hu).comp e.bijective

end Pi

section Cochains

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

def cT (m : BC F F') (T : C) : F.obj T →ₛₗ[algebraMap R S] F'.obj T where
  toFun := m.α T
  map_add' := map_add (m.α T)
  map_smul' := m.smul T

theorem liftSemi_cT_bijective (m : BC F F') (T : C) : Function.Bijective (liftSemi (cT m T)) := by
  obtain ⟨e, he⟩ := m.bij T
  have key : (liftSemi (cT m T) : S ⊗[R] F.obj T → F'.obj T) = e := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s b =>
      have h1 : s ⊗ₜ[R] b = s • ((1 : S) ⊗ₜ[R] b) := by simp [TensorProduct.smul_tmul']
      rw [liftSemi_tmul, h1, map_smul, he]
      rfl
  rw [key]
  exact e.bijective

theorem comparison_degree_zero_bijective [Finite C] (m : BC F F') : Function.Bijective (th0 m) :=
  liftSemi_piS_bijective (fun T ↦ cT m T) fun T ↦ liftSemi_cT_bijective m T

theorem comparison_degree_one_bijective [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    Function.Bijective (th1 m) :=
  liftSemi_piS_bijective (fun T ↦ piS fun T' ↦ piS fun _ : T ⟶ T' ↦ cT m T') fun _ ↦
    liftSemi_piS_bijective _ fun T' ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_cT_bijective m T'

theorem comparison_degree_two_bijective [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    Function.Bijective (th2 m) :=
  liftSemi_piS_bijective
    (fun T ↦ piS fun T' ↦ piS fun T'' ↦ piS fun _ : T ⟶ T' ↦ piS fun _ : T' ⟶ T'' ↦ cT m T'')
    fun _ ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_piS_bijective _ fun T'' ↦
      liftSemi_piS_bijective _ fun _ ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_cT_bijective m T''

end Cochains

theorem th_bijective (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P]
    [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F') :
    Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  haveI : Finite Pᵒᵖ := Finite.of_injective (Opposite.unop : Pᵒᵖ → P) Opposite.unop_injective
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun T T' ↦ inferInstance
  exact ⟨comparison_degree_zero_bijective m, comparison_degree_one_bijective m, comparison_degree_two_bijective m⟩

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DependencyStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq.Dep

open GlobalTheory.AbLaw (rs_rs rs_self)

variable {Y : Scheme.{0}}

theorem existsUnique_glue {I : Type} (O : I → Y.Opens) {W : Y.Opens} (hO : ∀ a, O a ≤ W)
    (hc : W ≤ ⨆ a, O a) (s : ∀ a, Γ(Y, O a))
    (h : ∀ a b, rs Y (inf_le_left : O a ⊓ O b ≤ O a) (s a) = rs Y inf_le_right (s b)) :
    ∃! t : Γ(Y, W), ∀ a, rs Y (hO a) t = s a :=
  Y.sheaf.existsUnique_gluing' O W (fun a => homOfLE (hO a)) hc s h

theorem exists_split {U : Y.Opens} (hU : IsAffineOpen U) {I : Type} (O : I → Y.Opens)
    (hO : ∀ a, O a ≤ U) (hc : U ≤ ⨆ a, O a) (φ : ∀ a b, Γ(Y, O a ⊓ O b))
    (hφ : ∀ a b d (W : Y.Opens) (ha : W ≤ O a) (hb : W ≤ O b) (hd : W ≤ O d),
      rs Y (le_inf ha hb) (φ a b) + rs Y (le_inf hb hd) (φ b d) = rs Y (le_inf ha hd) (φ a d)) :
    ∃ ψ : ∀ a, Γ(Y, O a), ∀ a b,
      φ a b = rs Y inf_le_left (ψ a) - rs Y inf_le_right (ψ b) := by
  have hM := ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB Y
  let ch : ∀ W : Y.Opens, GlobalTheory.AbLaw.SecOn (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB Y) W ≃ₗ[Γ(Y, W)] Γ(Y, W) :=
    fun W => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top
  have hr : ∀ {W W' : Y.Opens} (h : W' ≤ W) (s : GlobalTheory.AbLaw.SecOn (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB Y) W),
      ch W' (GlobalTheory.AbLaw.SecOn.restrict _ h s) = rs Y h (ch W s) := fun {W W'} h s =>
    GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top h s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU I O hO hc
    (fun a b => (ch _).symm (φ a b)) (by
      intro a b d W ha hb hd
      apply (ch W).injective
      rw [map_add (f := _), hr, hr, hr]
      simpa only [LinearEquiv.apply_symm_apply] using hφ a b d W ha hb hd)
  refine ⟨fun a => ch _ (ψ a), fun a b => ?_⟩
  have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
  rw [h, map_sub, hr, hr]

section Pot

variable {A : Type} (V : A → Y.Opens)

theorem cocycle_on {α : ∀ a b, Γ(Y, V a ⊓ V b)}
    (hα : ∀ a b d, rs Y (le₁₂ V a b d) (α a b) + rs Y (le₂₃ V a b d) (α b d) =
      rs Y (le₁₃ V a b d) (α a d))
    (a b d : A) (W : Y.Opens) (ha : W ≤ V a) (hb : W ≤ V b) (hd : W ≤ V d) :
    rs Y (le_inf ha hb) (α a b) + rs Y (le_inf hb hd) (α b d) = rs Y (le_inf ha hd) (α a d) := by
  have h := congrArg (rs Y (le_inf (le_inf ha hb) hd)) (hα a b d)
  simpa only [map_add (f := _), rs_rs] using h

def IsPot (α : ∀ a b, Γ(Y, V a ⊓ V b)) (U : Y.Opens) (p : ∀ a, Γ(Y, U ⊓ V a)) : Prop :=
  ∀ a b (W : Y.Opens) (h : W ≤ U) (ha : W ≤ V a) (hb : W ≤ V b),
    rs Y (le_inf h ha) (p a) - rs Y (le_inf h hb) (p b) = rs Y (le_inf ha hb) (α a b)

theorem exists_isPot (hV : ⨆ a, V a = ⊤) {α : ∀ a b, Γ(Y, V a ⊓ V b)}
    (hα : ∀ a b d, rs Y (le₁₂ V a b d) (α a b) + rs Y (le₂₃ V a b d) (α b d) =
      rs Y (le₁₃ V a b d) (α a d))
    {U : Y.Opens} (hU : IsAffineOpen U) : ∃ p, IsPot V α U p := by
  obtain ⟨ψ, hψ⟩ := exists_split hU (fun a => U ⊓ V a) (fun _ => inf_le_left)
    (GlobalTheory.AbLaw.CechOne.le_iSup_inf (hV.ge.trans' le_top))
    (fun a b => rs Y (inf_le_inf inf_le_right inf_le_right) (α a b)) (by
      intro a b d W ha hb hd
      simp only [rs_rs]
      exact cocycle_on V hα a b d W (ha.trans inf_le_right) (hb.trans inf_le_right)
        (hd.trans inf_le_right))
  refine ⟨ψ, fun a b W h ha hb => ?_⟩
  have e := congrArg (rs Y (le_inf (le_inf h ha) (le_inf h hb))) (hψ a b)
  simp only [map_sub, rs_rs] at e
  exact e.symm

variable {V}

theorem existsUnique_diff (hV : ⨆ a, V a = ⊤) {α : ∀ a b, Γ(Y, V a ⊓ V b)} {U W : Y.Opens}
    (h : W ≤ U) {p : ∀ a, Γ(Y, U ⊓ V a)} {q : ∀ a, Γ(Y, W ⊓ V a)} (hp : IsPot V α U p)
    (hq : IsPot V α W q) :
    ∃! f : Γ(Y, W), ∀ a, rs Y (inf_le_left : W ⊓ V a ≤ W) f =
      rs Y (inf_le_inf_right _ h) (p a) - q a := by
  refine existsUnique_glue (fun a => W ⊓ V a) (fun _ => inf_le_left)
    (GlobalTheory.AbLaw.CechOne.le_iSup_inf (hV.ge.trans' le_top)) _ fun a b => ?_
  have hW : W ⊓ V a ⊓ (W ⊓ V b) ≤ W := inf_le_left.trans inf_le_left
  have ha : W ⊓ V a ⊓ (W ⊓ V b) ≤ V a := inf_le_left.trans inf_le_right
  have hb : W ⊓ V a ⊓ (W ⊓ V b) ≤ V b := inf_le_right.trans inf_le_right
  have e1 := hp a b _ (hW.trans h) ha hb
  have e2 := hq a b _ hW ha hb
  simp only [map_sub, rs_rs]
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact e1.trans e2.symm

end Pot

section Coh

variable {k : Type} [Field k] (s : Y ⟶ Sp k) {A : Type} {V : A → Y.Opens}

theorem rs_cst {U W : Y.Opens} (h : W ≤ U) (c : k) :
    rs Y h (GlobalTheory.SmallExtLift.cst s U c) = GlobalTheory.SmallExtLift.cst s W c :=
  (Sec.res s h).commutes c

theorem smul_eq {U : Y.Opens} (c : k) (x : Γ(Y, U)) :
    @HSMul.hSMul k (Sec s U) (Sec s U) _ c x = GlobalTheory.SmallExtLift.cst s U c * x :=
  Algebra.smul_def (A := Sec s U) c x

variable {α : ∀ a b, Γ(Y, V a ⊓ V b)} (hV : ⨆ a, V a = ⊤)
  {P : ∀ T : Y.affineOpens, ∀ a, Γ(Y, T.1 ⊓ V a)} (hP : ∀ T, IsPot V α T.1 (P T))

def diffF (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) : Γ(Y, T'.1) :=
  (existsUnique_diff hV h (hP T) (hP T')).choose

theorem diffF_spec (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) (a : A) :
    rs Y (inf_le_left : T'.1 ⊓ V a ≤ T'.1) (diffF hV hP T T' h) =
      rs Y (inf_le_inf_right _ h) (P T a) - P T' a :=
  (existsUnique_diff hV h (hP T) (hP T')).choose_spec.1 a

theorem diffF_comp (T T' T'' : Y.affineOpens) (h : T'.1 ≤ T.1) (h' : T''.1 ≤ T'.1) :
    diffF hV hP T T'' (h'.trans h) = rs Y h' (diffF hV hP T T' h) + diffF hV hP T' T'' h' := by
  refine (existsUnique_diff hV (h'.trans h) (hP T) (hP T'')).unique
    (existsUnique_diff hV (h'.trans h) (hP T) (hP T'')).choose_spec.1 fun a => ?_
  have e1 := congrArg (rs Y (inf_le_inf_right (V a) h')) (diffF_spec hV hP T T' h a)
  have e2 := diffF_spec hV hP T' T'' h' a
  simp only [map_sub, rs_rs] at e1
  rw [map_add (f := _), rs_rs, e2]
  rw [show rs Y _ (diffF hV hP T T' h) = _ from e1]
  abel

def diffZ : CatCoh.Z1 (OAff s) :=
  ⟨fun T T' φ => diffF hV hP T.unop T'.unop (leOfHom φ.unop), fun _ _ _ φ ψ =>
    diffF_comp hV hP _ _ _ (leOfHom φ.unop) (leOfHom ψ.unop)⟩

end Coh

end GlobalTheory.CompanionTheory.FewEq.Dep

namespace GlobalTheory.CompanionTheory.FewEq

open Dep
open GlobalTheory.AbLaw (rs_rs rs_self)

theorem depSt : DepSt := by
  intro k _ Y s₀ hsep n r hfin hle hnr A V hV hVa α hα
  have hex := fun (i : Fin r) (T : Y.affineOpens) => exists_isPot V hV (hα i) T.2
  choose p hp using hex
  let f : Fin r → CatCoh.Z1 (OAff s₀) := fun i => diffZ s₀ hV (hp i)
  have hnot : ¬ LinearIndependent k (fun i => CatCoh.H1.mk (OAff s₀) (f i)) := fun hli => by
    have : r ≤ Module.finrank k (HO1 s₀) :=
      (Fintype.card_fin r).symm.le.trans hli.fintype_card_le_finrank
    omega
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnot
  have h0 : CatCoh.H1.mk (OAff s₀) (∑ i, c i • f i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [map_smul] using hc
  obtain ⟨g, hg⟩ := CatCoh.H1.mk_eq_zero.1 h0
  obtain ⟨G, hG⟩ : ∃ G : ∀ T : Y.affineOpens, Γ(Y, T.1), ∀ (T T' : Y.affineOpens) (h : T'.1 ≤ T.1),
      G T' - rs Y h (G T) = ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * diffF hV (hp i) T T' h := by
    refine ⟨fun T => g (Opposite.op T), fun T T' h => ?_⟩
    have e := congrFun (congrFun (congrFun hg (Opposite.op T)) (Opposite.op T'))
      (homOfLE (show T' ≤ T from h)).op
    let ev : CatCoh.Z1 (OAff s₀) →+ Γ(Y, T'.1) :=
      { toFun := fun z => z.1 (Opposite.op T) (Opposite.op T') (homOfLE (show T' ≤ T from h)).op
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact e.trans ((map_sum ev (fun i => c i • f i) Finset.univ).trans
      (Finset.sum_congr rfl fun i _ => smul_eq s₀ (c i) _))
  let P : ∀ T : Y.affineOpens, ∀ a, Γ(Y, T.1 ⊓ V a) := fun T a =>
    ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * p i T a + rs Y inf_le_left (G T)
  have hPot : ∀ (T : Y.affineOpens) (a b : A) (W : Y.Opens) (h : W ≤ T.1) (ha : W ≤ V a)
      (hb : W ≤ V b), rs Y (le_inf h ha) (P T a) - rs Y (le_inf h hb) (P T b) =
        rs Y (le_inf ha hb) (∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * α i a b) := by
    intro T a b W h ha hb
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_add (f := _), map_sum, map_mul, rs_rs, rs_cst]
    simp only [← hp _ T a b W h ha hb, mul_sub, Finset.sum_sub_distrib]
    ring
  have hPres : ∀ (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) (a : A),
      rs Y (inf_le_inf_right _ h) (P T a) = P T' a := by
    intro T T' h a
    have e := congrArg (rs Y (inf_le_left : T'.1 ⊓ V a ≤ T'.1)) (hG T T' h)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, rs_rs, rs_cst, diffF_spec, mul_sub,
      Finset.sum_sub_distrib] at e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_add (f := _), map_sum, map_mul, rs_rs, rs_cst]
    linear_combination -e
  refine ⟨c, fun a => rs Y (le_inf le_rfl le_rfl) (P ⟨V a, hVa a⟩ a),
    fun h => hi₀ (by rw [h]; rfl), fun a b => ?_⟩
  let T' : Y.affineOpens := ⟨V a ⊓ V b, IsAffineOpen.inf (hVa a) (hVa b)⟩
  have e := hPot T' a b T'.1 le_rfl inf_le_left inf_le_right
  rw [← hPres ⟨V a, hVa a⟩ T' inf_le_left a, ← hPres ⟨V b, hVa b⟩ T' inf_le_right b] at e
  simp only [rs_rs] at e ⊢
  rw [rs_self] at e
  exact e.symm

end GlobalTheory.CompanionTheory.FewEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFactorOfExactIsField
section
open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

theorem exists_factor_of_exact_field {K A B D : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup D] [Module K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] D) (hfg : Function.Exact f g) (μ : B →ₗ[K] K)
    (hμ : ∀ a, μ (f a) = 0) : ∃ ρ : D →ₗ[K] K, μ = ρ ∘ₗ g := by
  have hle : LinearMap.ker g ≤ LinearMap.ker μ := by
    intro b hb
    obtain ⟨a, rfl⟩ := (hfg b).1 hb
    exact hμ a
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_extend
    ((LinearMap.ker g).liftQ μ hle ∘ₗ (g.quotKerEquivRange.symm : LinearMap.range g →ₗ[K] B ⧸ LinearMap.ker g))
  refine ⟨ρ, LinearMap.ext fun b => ?_⟩
  have hb := LinearMap.congr_fun hρ ⟨g b, LinearMap.mem_range_self g b⟩
  calc μ b = (LinearMap.ker g).liftQ μ hle ((LinearMap.ker g).mkQ b) := by
        rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
    _ = (LinearMap.ker g).liftQ μ hle
          (g.quotKerEquivRange.symm ⟨g b, LinearMap.mem_range_self g b⟩) := by
        rw [LinearMap.quotKerEquivRange_symm_apply_image]
    _ = ρ (g b) := hb.symm

theorem exists_factor_of_exact_isField {K A B D : Type} [CommRing K] (hK : IsField K)
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup D] [Module K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] D) (hfg : Function.Exact f g) (μ : B →ₗ[K] K)
    (hμ : ∀ a, μ (f a) = 0) : ∃ ρ : D →ₗ[K] K, μ = ρ ∘ₗ g := by
  letI := hK.toField
  exact exists_factor_of_exact_field f g hfg μ hμ

theorem exists_rho_of_exact {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hR : IsField R)
    (hex : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0))
    (ν ν₀ : Cn F 0 →ₗ[R] R) (h1 : ν₀ 1 = 1) :
    ∃ ρ : Cn F 1 →ₗ[R] R, ν = ν 1 • ν₀ + ρ ∘ₗ dn F 0 := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.CompanionTheory.HopfLe.exists_factor_of_exact_isField hR _ _ hex (ν - ν 1 • ν₀) (by
    intro r
    simp only [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply,
      LinearMap.smul_apply, map_smul, h1, smul_eq_mul, mul_one]
    ring)
  refine ⟨ρ, ?_⟩
  rw [← hρ]
  abel

end GlobalTheory.CompanionTheory.HopfLe
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGeneralizedInverseOfUnitKernel
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_generalisedInverse_of_fibre_ker_span :
    ∀ (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [Module.Finite R P₀] [Module.Projective R P₀] [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁] (a₀ : P₀ →ₗ[R] P₁) (e : P₀), a₀ e = 0 → (∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e)) → ∃ t : P₁ →ₗ[R] P₀, a₀ ∘ₗ t ∘ₗ a₀ = a₀ := by
  intro R P₀ P₁ _ _ _ _ _ _ _ _ _ a₀ e he hker
  have hcomp : a₀ ∘ₗ LinearMap.toSpanSingleton R P₀ e = 0 := by
    ext
    simp [he]
  have hexact : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Exact (LinearMap.lTensor m.ResidueField (LinearMap.toSpanSingleton R P₀ e))
        (LinearMap.lTensor m.ResidueField a₀) := by
    intro m _ y
    constructor
    · intro hy
      obtain ⟨c, rfl⟩ := hker m.ResidueField y hy
      refine ⟨c ⊗ₜ[R] (1 : R), ?_⟩
      rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul,
        TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rintro ⟨z, rfl⟩
      rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨s, t, hst⟩ := GlobalTheory.exists_homotopy_of_forall_exact_residueField hcomp hexact
  refine ⟨t, LinearMap.ext fun x => ?_⟩
  have hx : LinearMap.toSpanSingleton R P₀ e (s x) + t (a₀ x) = x := LinearMap.congr_fun hst x
  have htx : t (a₀ x) = x - LinearMap.toSpanSingleton R P₀ e (s x) := eq_sub_of_add_eq' hx
  show a₀ (t (a₀ x)) = a₀ x
  rw [htx, map_sub, LinearMap.toSpanSingleton_apply, map_smul, he, smul_zero, sub_zero]

end GlobalTheory.CompanionTheory.PerfVB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyDataCohomologyBaseChange
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.PerfVB.ContrBC

theorem nonempty_Hc_equiv_of_contraction {S A B C H : Type} [CommRing S] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module S A] [Module S B] [Module S C]
    [Module S H] (f : A →ₗ[S] B) (g : B →ₗ[S] C) (j : H →ₗ[S] B) (π : B →ₗ[S] H)
    (h : B →ₗ[S] A) (h' : C →ₗ[S] B) (hπj : π ∘ₗ j = LinearMap.id) (hgj : g ∘ₗ j = 0)
    (hπf : π ∘ₗ f = 0) (hc : j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id) :
    Nonempty (Hc f g ≃ₗ[S] H) := by
  have hgj' : ∀ y, j y ∈ LinearMap.ker g := fun y => LinearMap.mem_ker.2 (LinearMap.congr_fun hgj y)
  have hπj' : ∀ y, π (j y) = y := fun y => LinearMap.congr_fun hπj y
  have hπf' : ∀ x, π (f x) = 0 := fun x => LinearMap.congr_fun hπf x
  have hc' : ∀ b, j (π b) + f (h b) + h' (g b) = b := fun b => LinearMap.congr_fun hc b
  have hle : Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) ≤
      LinearMap.ker (π ∘ₗ (LinearMap.ker g).subtype) := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨x, rfl⟩ : ∃ x, f x = z := LinearMap.mem_range.1 (Submodule.mem_comap.1 hzN)
    rw [LinearMap.mem_ker]
    exact hπf' x
  refine ⟨LinearEquiv.ofLinear (Submodule.liftQ _ (π ∘ₗ (LinearMap.ker g).subtype) hle)
    ((Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f)).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker g) j hgj') ?_ ?_⟩
  · refine LinearMap.ext fun y => ?_
    exact hπj' y
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f)) q
    have hz' : g z = 0 := LinearMap.mem_ker.1 hz
    have e : z = j (π z) + f (h z) := by
      have := hc' z
      rw [hz', map_zero, add_zero] at this
      exact this.symm
    have key : (⟨j (π z), hgj' (π z)⟩ : LinearMap.ker g) - ⟨z, hz⟩ ∈
        Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) := by
      refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨-h z, ?_⟩)
      change f (-h z) = j (π z) - z
      calc f (-h z) = -f (h z) := map_neg _ _
        _ = j (π z) - (j (π z) + f (h z)) := by abel
        _ = j (π z) - z := by rw [← e]
    exact (Submodule.Quotient.eq _).2 key

theorem nonempty_Hc_baseChange_equiv (R A B C H S : Type) [CommRing R] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C]
    [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B)
    (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B) (_hgf : g ∘ₗ f = 0)
    (hπj : π ∘ₗ j = LinearMap.id) (hgj : g ∘ₗ j = 0) (hπf : π ∘ₗ f = 0)
    (hc : j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id) :
    Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  refine nonempty_Hc_equiv_of_contraction (f.baseChange S) (g.baseChange S) (j.baseChange S)
    (π.baseChange S) (h.baseChange S) (h'.baseChange S) ?_ ?_ ?_ ?_
  · rw [← LinearMap.baseChange_comp, hπj, LinearMap.baseChange_id]
  · rw [← LinearMap.baseChange_comp, hgj, LinearMap.baseChange_zero]
  · rw [← LinearMap.baseChange_comp, hπf, LinearMap.baseChange_zero]
  · rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_add, ← LinearMap.baseChange_add, hc, LinearMap.baseChange_id]

end GlobalTheory.CompanionTheory.PerfVB.ContrBC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfModelsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_of_models : (∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f → ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M) → GlobalTheory.SpreadingModels.PerfAll := by
  first | exact @GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel | exact GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel | (intros; apply GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel <;> assumption)
end

