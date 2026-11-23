module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFixedNearOneSiegelParabolic
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open Filter Topology

namespace GlobalTheory.KSp.ParNear

variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (M N : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (h : N.toBlocks₂₁ = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, h, fromBlocks_multiply]
  simp

theorem toBlocks₁₁_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
  ext i j; simp [toBlocks₁₁, Matrix.one_apply]

theorem toBlocks₁₂_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
  ext i j; simp [toBlocks₁₂, one_apply]

variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]

theorem mat_one : mat c (1 : UG c (stdJ ν E)) = 1 := rfl

theorem mat_mul_mat_inv (g : UG c (stdJ ν E)) : mat c g * mat c g⁻¹ = 1 := by
  change (((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
  rw [mul_inv_cancel]; rfl

theorem pr_zero_right (Q : Matrix α α E) (x : Matrix α ν E) : pr c Q x 0 = 0 := by
  simp [pr, form, GlobalTheory.WeilM.hTens]

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]

theorem continuous_mat : Continuous fun g : UG c (stdJ ν E) => mat c g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mat_inv : Continuous fun g : UG c (stdJ ν E) => mat c g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_pr (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E) :
    Continuous fun p : Matrix α ν E × Matrix α ν E => pr c Q p.1 p.2 := by
  simp only [pr, form, GlobalTheory.WeilM.hTens]
  refine continuous_const.mul (htr.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_))
  refine Continuous.mul (Continuous.mul (Continuous.mul ?_ continuous_const) continuous_const) (hc.comp ?_)
  · rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact continuous_const
  · rcases l with l | l
    · exact continuous_const
    · exact continuous_snd.matrix_elem k l

theorem continuous_pr_comp (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E)
    {X : Type} [TopologicalSpace X] {f g : X → Matrix α ν E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => pr c Q (f x) (g x) := by
  have h := (continuous_pr (ν := ν) c hc htr Q).comp (hf.prodMk hg)
  exact h

end GlobalTheory.KSp.ParNear

theorem GlobalTheory.KSp.parFun_fixed_near_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ hψ _ _ χ hχ _ φ hφ
  obtain ⟨-, htop, -, -, hcc, -, htr, -⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  haveI := htop
  haveI := GlobalTheory.WeilM.nonarch_field F
  have hψl := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ
  have hφl : IsLocallyConstant φ := hφ.1
  have hK : IsCompact (tsupport φ) := hφ.2
  have hA : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hB : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₂ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hA' : Continuous fun g : UG c (stdJ ν E) => (mat c g⁻¹).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat_inv c).matrix_elem _ _

  have hi : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), sc F χ (Fintype.card α) (mat c g).toBlocks₁₁.det = 1 := by
    have ht : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁.det) (𝓝 1) (𝓝 1) := by
      have := hA.matrix_det.tendsto 1
      rwa [GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', det_one] at this
    exact ht.eventually (_root_.GlobalTheory.KSp.sc_eventually_eq_one F E c δ hE _ χ hχ)

  have hii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ x ∈ tsupport φ,
      ψ (2⁻¹ * pr c Q (x * (mat c g).toBlocks₁₁) (x * (mat c g).toBlocks₁₂)) * φ (x * (mat c g).toBlocks₁₁) = φ x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have hP : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      GlobalTheory.KSp.ParNear.continuous_pr_comp c hcc htr Q (continuous_snd.matrix_mul (hA.comp continuous_fst))
        (continuous_snd.matrix_mul (hB.comp continuous_fst))
    have hP2 : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        (2 : F)⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      continuous_const.mul hP
    have h1 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E =>
        ψ (2⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂)) :=
      hψl.comp_continuous hP2
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x), h3.eventually_eq (1, x)] with p e1 e2 e3
    rw [e1, e2, e3, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', GlobalTheory.KSp.ParNear.toBlocks₁₂_one', Matrix.mul_one, Matrix.mul_zero,
      GlobalTheory.KSp.ParNear.pr_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul]

  have hiii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ y ∈ tsupport φ, φ (y * (mat c g⁻¹).toBlocks₁₁) = φ y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1⁻¹).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA'.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h2.eventually_eq (1, y), h3.eventually_eq (1, y)] with p e2 e3
    rw [e2, e3, inv_one, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', Matrix.mul_one]
  filter_upwards [hi, hii, hiii] with g hg1 hg2 hg3 hg
  have hinv : (mat c g).toBlocks₁₁ * (mat c g⁻¹).toBlocks₁₁ = 1 := by
    rw [← GlobalTheory.KSp.ParNear.toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero _ _ ((GlobalTheory.KSp.mem_sieg c).mp ((sieg c ν).inv_mem hg)),
      GlobalTheory.KSp.ParNear.mat_mul_mat_inv, GlobalTheory.KSp.ParNear.toBlocks₁₁_one']
  funext x
  simp only [parFun]
  rw [hg1, one_mul]
  by_cases hx : x ∈ tsupport φ
  · exact hg2 x hx
  · rw [image_eq_zero_of_notMem_tsupport hx]
    by_contra hne
    have hne' : φ (x * (mat c g).toBlocks₁₁) ≠ 0 := right_ne_zero_of_mul hne
    have hy : x * (mat c g).toBlocks₁₁ ∈ tsupport φ := subset_tsupport _ hne'
    have e := hg3 _ hy
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one] at e
    exact hx (subset_tsupport _ (by rw [Function.mem_support, e]; exact hne'))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

open scoped TensorProduct

namespace GlobalTheory.EtC.TensLocBij

theorem locAll {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) :
    Loc U P := GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

theorem locMono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

theorem locAnd {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.1 U P Q hP hQ

theorem locTrans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

theorem locFin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

section Alg

variable {S : Type*} [CommRing S] {A B D : Type*} [AddCommGroup A] [Module S A]
  [AddCommGroup B] [Module S B] [AddCommGroup D] [Module S D]

theorem exists_fg_lTensor (x : A ⊗[S] B) :
    ∃ (J : Submodule S B) (_ : J.FG) (y : A ⊗[S] J), x = LinearMap.lTensor A J.subtype y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Submodule.fg_bot, 0, by simp⟩
  | tmul a b => exact ⟨S ∙ b, Submodule.fg_span_singleton b,
      a ⊗ₜ[S] ⟨b, Submodule.mem_span_singleton_self _⟩, rfl⟩
  | add x₁ x₂ ih₁ ih₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ih₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ih₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂, LinearMap.lTensor A (Submodule.inclusion le_sup_left) y₁ +
      LinearMap.lTensor A (Submodule.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add (f := _), ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl

theorem rTensor_comm_eq {Y : Type*} [AddCommGroup Y] [Module S Y] (g : B →ₗ[S] Y) (x : A ⊗[S] B) :
    LinearMap.rTensor A g (TensorProduct.comm S A B x) =
      TensorProduct.comm S A Y (LinearMap.lTensor A g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fg_lTensor_eq_zero {J : Submodule S D} (hJ : J.FG) {t : A ⊗[S] J}
    (h : LinearMap.lTensor A J.subtype t = 0) :
    ∃ (K : Submodule S D) (hJK : J ≤ K), K.FG ∧
      LinearMap.lTensor A (Submodule.inclusion hJK) t = 0 := by
  have h' : LinearMap.rTensor A J.subtype (TensorProduct.comm S A J t) = 0 := by
    rw [rTensor_comm_eq, h, map_zero]
  obtain ⟨K, hJK, hK, h0⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hJ h'
  refine ⟨K, hJK, hK, ?_⟩
  rw [rTensor_comm_eq] at h0
  exact (LinearEquiv.map_eq_zero_iff _).mp h0

end Alg

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

theorem surj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (U : Scheme.{0}) (y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U))) :
    Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x =
      TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y := by
  induction y using TensorProduct.induction_on with
  | zero => exact locAll fun V g => ⟨0, by simp⟩
  | tmul c q =>
    exact locMono (hs U q) fun V g ⟨x, hx⟩ => ⟨(C.map g.op).hom c ⊗ₜ x, by simp [hx]⟩
  | add a b ha hb =>
    exact locMono (locAnd ha hb) fun V g ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ => ⟨x + x', by simp [map_add (f := _), hx, hx']⟩

theorem kerPart
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (V : Scheme.{0}) (K : Submodule (ULift.{1} R) (P.obj (op V)))
    (hK : ∀ k ∈ K, (φ.app (op V)).hom k = 0) (z : C.obj (op V) ⊗[ULift.{1} R] K) :
    Loc V fun _ h => TensorProduct.map (C.map h.op).hom (P.map h.op).hom
      (LinearMap.lTensor _ K.subtype z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact locAll fun _ _ => by simp
  | tmul c k => exact locMono (hi V k.1 (hK k.1 k.2)) fun W h hk => by simp [hk]
  | add a b ha hb => exact locMono (locAnd ha hb) fun W h ⟨h1, h2⟩ => by simp [map_add (f := _), h1, h2]

theorem map_restr_comp {U V W : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) :
    TensorProduct.map (C.map (k ≫ g).op).hom (P.map (k ≫ g).op).hom =
      TensorProduct.map (C.map k.op).hom (P.map k.op).hom ∘ₗ
        TensorProduct.map (C.map g.op).hom (P.map g.op).hom := by
  rw [op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    TensorProduct.map_comp]

theorem nat_apply {U V : Scheme.{0}} (g : V ⟶ U) (p : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom p) = (Q.map g.op).hom ((φ.app (op U)).hom p) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h p) (φ.naturality g.op)
  simpa using this

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

theorem inj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)))
    (hx : LinearMap.lTensor _ (φ.app (op U)).hom x = 0) :
    Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  obtain ⟨B₀, hB₀, x₀, rfl⟩ := exists_fg_lTensor x
  have hcomp : (B₀.map (φ.app (op U)).hom).subtype ∘ₗ (φ.app (op U)).hom.submoduleMap B₀ =
      (φ.app (op U)).hom ∘ₗ B₀.subtype := rfl
  have ht : LinearMap.lTensor _ (B₀.map (φ.app (op U)).hom).subtype
      (LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) x₀) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨K, hJK, ⟨s, hs'⟩, hK0⟩ := fg_lTensor_eq_zero (hB₀.map _) ht
  have hloc := locFin (ι := Fin s.card)
    (fun i V g => ∃ p, (φ.app (op V)).hom p = (Q.map g.op).hom (s.equivFin.symm i).1)
    (fun i => hs U (s.equivFin.symm i).1)
  apply locTrans
  refine locMono hloc fun V g hV => ?_
  have hle : K ≤ (LinearMap.range (φ.app (op V)).hom).comap (Q.map g.op).hom := by
    rw [← hs', Submodule.span_le]
    intro q hq
    obtain ⟨p, hp⟩ := hV (s.equivFin ⟨q, hq⟩)
    rw [Equiv.symm_apply_apply] at hp
    exact ⟨p, hp⟩
  let ρ := ((Q.map g.op).hom ∘ₗ K.subtype).codRestrict (LinearMap.range (φ.app (op V)).hom)
    (fun k => hle k.2)
  have key : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict ∘ₗ
      TensorProduct.map (C.map g.op).hom (P.map g.op).hom ∘ₗ LinearMap.lTensor _ B₀.subtype =
      TensorProduct.map (C.map g.op).hom ρ ∘ₗ LinearMap.lTensor _ (Submodule.inclusion hJK) ∘ₗ
        LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul]
    congr 1
    apply Subtype.ext
    simp [ρ, nat_apply]
  have hy : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict
      (TensorProduct.map (C.map g.op).hom (P.map g.op).hom (LinearMap.lTensor _ B₀.subtype x₀)) = 0 := by
    have := congrArg (fun L => L x₀) key
    simp only [LinearMap.comp_apply] at this
    rw [this, hK0, map_zero]
  have hex := lTensor_exact (C.obj (op V))
    (LinearMap.exact_subtype_ker_map (φ.app (op V)).hom.rangeRestrict)
    (LinearMap.surjective_rangeRestrict _)
  obtain ⟨z, hz⟩ := (hex _).mp hy
  have hK : ∀ k ∈ LinearMap.ker (φ.app (op V)).hom.rangeRestrict, (φ.app (op V)).hom k = 0 := by
    intro k hk
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hk)
    simpa using this
  refine locMono (kerPart C P Q φ hi V _ hK z) fun W k hk => ?_
  rw [map_restr_comp, LinearMap.comp_apply, ← hz]
  exact hk

theorem main : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  fun _ _ C P Q φ hs hi U => ⟨surj C P Q φ hs U, inj C P Q φ hs hi U⟩

end GlobalTheory.EtC.TensLocBij

theorem GlobalTheory.EtC.tensor_loc_bij : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  GlobalTheory.EtC.TensLocBij.main
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralNormProdExpMulLeHaar
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

open scoped Pointwise

theorem GlobalTheory.setIntegral_norm_prodExp_mul_le_haar : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ ρ > 0, ∀ K₁ : Set G, IsCompact K₁ → ∃ (C : ℝ) (K₂ : Set G), 0 ≤ C ∧ IsCompact K₂ ∧ ∀ φ : G → ℂ, Continuous φ → ∀ y ∈ K₁, ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ, ‖φ (h.prodExp b t * y)‖ ≤ C * ∫ x in K₂, ‖φ x‖ ∂μ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ
  haveI := hμ
  haveI : LocallyCompactSpace G := IsExpLieAlgebra.locallyCompactSpace h
  haveI : SecondCountableTopology 𝔸ˣ := Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  haveI : SecondCountableTopology G := Topology.IsInducing.subtypeVal.secondCountableTopology
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp_tsupport μ b
  refine ⟨ε / 2, by positivity, fun K₁ hK₁ => ?_⟩
  let β : ContDiffBump (0 : Fin d → ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  set K : (Fin d → ℝ) → ℂ := fun t => ((β t : ℝ) : ℂ) with hKdef
  have hK : ContDiff ℝ ∞ K := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hKs : tsupport K ⊆ Metric.closedBall 0 ε := by
    have : tsupport K ⊆ tsupport β := tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) _
    rw [β.tsupport_eq] at this
    exact this
  obtain ⟨κ, hκs, hκc, -, hκint⟩ := hdens K hK hKs
  have hκcont : Continuous κ := by
    letI := h.chartedSpace
    exact hκs.continuous
  obtain ⟨M, hM⟩ := hκc.exists_bound_of_continuous hκcont
  have hK₂ : IsCompact (tsupport κ * K₁) := IsCompact.mul hκc hK₁
  obtain ⟨B, hB⟩ := GlobalTheory.T.haar_lintegral_mul_right_le_alt G μ hμ K₁ hK₁
  refine ⟨max M 0 * B, tsupport κ * K₁, by positivity, hK₂, fun φ hφ y hy => ?_⟩
  set K₂ := tsupport κ * K₁ with hK₂def
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  set f : (Fin d → ℝ) → ℝ := fun t => ‖φ (P t * y)‖ with hfdef
  have hfc : Continuous f := (hφ.comp (hPc.mul continuous_const)).norm
  set ψ : G → ℂ := fun x => ((‖φ (x * y)‖ : ℝ) : ℂ) with hψdef
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp (hφ.comp (continuous_id.mul continuous_const)).norm

  have h1 : ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), f t ≤ ∫ t, β t * f t := by
    have e : ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), f t
        = ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), β t * f t := by
      refine setIntegral_congr_fun measurableSet_closedBall fun t ht => ?_
      rw [β.one_of_mem_closedBall ht, one_mul]
    rw [e]
    refine setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun t => mul_nonneg β.nonneg (norm_nonneg _))
    exact (β.continuous.mul hfc).integrable_of_hasCompactSupport β.hasCompactSupport.mul_right

  have h2 : ∫ t, β t * f t = (∫ x, κ x * ψ x ∂μ).re := by
    rw [hκint ψ hψc]
    have : (fun t => K t * ψ (P t)) = fun t => (((β t * f t : ℝ)) : ℂ) := by
      funext t; simp [hKdef, hψdef, hfdef]
    rw [this, integral_complex_ofReal, Complex.ofReal_re]

  have h3 : (∫ x, κ x * ψ x ∂μ).re ≤ ∫ x, ‖κ x * ψ x‖ ∂μ :=
    (Complex.re_le_norm _).trans (norm_integral_le_integral_norm _)

  set g : G → ENNReal := K₂.indicator fun z => ‖φ z‖ₑ with hgdef
  have hg : Measurable g := hφ.enorm.measurable.indicator hK₂.isClosed.measurableSet
  set L := ∫⁻ x in K₂, ‖φ x‖ₑ ∂μ with hLdef
  have hL : L < ⊤ := (hφ.continuousOn.integrableOn_compact hK₂).hasFiniteIntegral
  have hgL : ∫⁻ x, g x ∂μ = L := lintegral_indicator hK₂.isClosed.measurableSet _
  have hpt : ∀ x, ‖κ x * ψ x‖ₑ ≤ ENNReal.ofReal (max M 0) * g (x * y) := by
    intro x
    by_cases hx : x ∈ tsupport κ
    · have hxy : x * y ∈ K₂ := Set.mul_mem_mul hx hy
      rw [hgdef, Set.indicator_of_mem hxy, enorm_mul]
      gcongr
      · rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal ((hM x).trans (le_max_left _ _))
      · rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        apply le_of_eq
        congr 1
        simp [hψdef]
    · have : κ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have h4l : ∫⁻ x, ‖κ x * ψ x‖ₑ ∂μ ≤ ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) := by
    calc ∫⁻ x, ‖κ x * ψ x‖ₑ ∂μ ≤ ∫⁻ x, ENNReal.ofReal (max M 0) * g (x * y) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal (max M 0) * ∫⁻ x, g (x * y) ∂μ :=
          lintegral_const_mul _ (hg.comp (measurable_id.mul_const y))
      _ ≤ ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) := by
          gcongr
          rw [← hgL]
          exact hB y hy g hg
  have h4 : ∫ x, ‖κ x * ψ x‖ ∂μ ≤ max M 0 * B * ∫ x in K₂, ‖φ x‖ ∂μ := by
    rw [integral_norm_eq_lintegral_enorm (f := fun x => κ x * ψ x) (hκcont.mul hψc).aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm hφ.aestronglyMeasurable]
    have hfin : ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hL.ne)
    refine (ENNReal.toReal_mono hfin h4l).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_max_right _ _),
      ENNReal.coe_toReal, mul_assoc]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ ≤ _ := h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialCochain_coboundary_of_class_zero :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
      (s : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F),
      IsCls (R := R) s (0 : H R E F ((1 : ℕ) : ℤ)) →
        ∃ t : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, s = cobd (R := R) (E := E) (n := 0) t := by
  intro R _ F E s hs
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := _root_.GlobalTheory.EtC.res_basic R F
  obtain ⟨z, hz0, hz⟩ := hs
  rw [CohomologyClass.mk_eq_zero_iff] at hz0
  obtain ⟨m, hm, β, hβ⟩ := hz0
  obtain rfl : m = 0 := by push_cast at hm; omega
  have hzv : ∀ (p q : ℤ) (hpq : p + ((1 : ℕ) : ℤ) = q),
      (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)).v p q hpq =
        (Cochain.single (p := -((1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E 1).hom ≫ s ≫ resι R F) ((1 : ℕ) : ℤ)).v p q hpq := by
    intro p q hpq
    rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)) = z.1 from rfl, hz]
  let b := β.v 0 0 (by omega)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v hβ 0 1 (by norm_num)
    rw [δ_v 0 _ (by norm_num) β 0 1 _ 0 1 (by omega) rfl,
      (hpos E 1 (by norm_num)).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero, hzv,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
    exact e
  have : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  have e := Cochain.congr_v hβ (-((1 : ℕ) : ℤ)) 0 (by omega)
  have h1 : β.v (-((1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
  rw [δ_v 0 _ (by norm_num) β _ 0 _ (-1) 0 (by omega) (by norm_num), h1,
    zero_comp, zero_add, hzv, Cochain.single_v] at e
  rw [show β.v 0 0 (by omega) = b from rfl, ← ht'] at e
  let D : (free R).obj (E.obj (op ⦋1⦌)) ⟶ (free R).obj (E.obj (op ⦋0⦌)) :=
    ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
  have hd : ((chains R).obj E).d (-((1 : ℕ) : ℤ)) 0 = (chainsXIso R E 1).hom ≫ D ≫ (chainsXIso R E 0).inv :=
    GlobalTheory.EtC.ClsBasic.chains_d (R := R) E 0
  rw [hd] at e
  have hs_eq : s = (((1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E 0).inv ≫ t') := by
    apply (cancel_epi (chainsXIso R E 1).hom).1
    apply (cancel_mono (resι R F)).1
    rw [Category.assoc, ← e]
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  refine ⟨(((1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E 0).inv ≫ t'), ?_⟩
  rw [hs_eq]
  simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
    smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsLimitWidePullbackStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_widePushout_isLimit_widePullback : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i]))) := by
  first | exact @GlobalTheory.spec_widePushout_isLimit | exact GlobalTheory.spec_widePushout_isLimit | (intros; apply GlobalTheory.spec_widePushout_isLimit; all_goals assumption)
end

