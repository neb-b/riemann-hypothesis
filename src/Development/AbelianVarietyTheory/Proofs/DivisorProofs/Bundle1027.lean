module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open GlobalTheory.LB (resG_resG resG_self homOfLinear)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.DualPull

variable {X Y : Scheme.{0}}

abbrev cutO (T W : Y.Opens) : Y.Opens := T.ι ''ᵁ T.ι ⁻¹ᵁ W

theorem cutO_le (T W : Y.Opens) : cutO T W ≤ W := T.ι.image_preimage_le W

theorem cutO_le' (T W : Y.Opens) : cutO T W ≤ T := T.ι_image_le _

theorem le_cutO {T W S : Y.Opens} (h : S ≤ T) (h' : S ≤ W) : S ≤ cutO T W := by
  rw [cutO, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf h h'

theorem cutO_mono (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) : cutO T W' ≤ cutO T W :=
  le_cutO (cutO_le' _ _) ((cutO_le _ _).trans h)

def cut (T : Y.Opens) : Y.Modules :=
  (Scheme.Modules.pushforward T.ι).obj ((structureModule Y).restrict T.ι)

def cutEquiv (T W : Y.Opens) : Γ(cut T, W) ≃+ Γ(Y, cutO T W) := AddEquiv.refl _

theorem cutEquiv_smul (T W : Y.Opens) (a : Γ(Y, W)) (s : Γ(cut T, W)) :
    cutEquiv T W (a • s) = resG Y (cutO_le T W) a * cutEquiv T W s :=
  congrArg (· * cutEquiv T W s) congr($(T.ι.app_appIso_inv W) a)

theorem cutEquiv_res (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) (s : Γ(cut T, W)) :
    cutEquiv T W' (resM (cut T) h s) = resG Y (cutO_mono T h) (cutEquiv T W s) := rfl

variable {P : Y.Modules} {T : Y.Opens}

def toCut (l : Γ(dual P, T)) : P ⟶ cut T :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv T W).symm (dualApp l (cutO_le' T W) (resM P (cutO_le T W) s))
      map_add' s t := by simp only [map_add (f := _)]
      map_smul' a s := (cutEquiv T W).injective (by
        rw [RingHom.id_apply, cutEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul]) })
    fun {W W'} h s => (cutEquiv T W').injective (by
      change dualApp l _ (resM P _ (resM P h s)) = resG Y (cutO_mono T h) (dualApp l _ (resM P _ s))
      rw [← dualApp_resM, resM_resM, resM_resM])

theorem toCut_app (l : Γ(dual P, T)) (W : Y.Opens) (s : Γ(P, W)) :
    cutEquiv T W ((toCut l).app W s) = dualApp l (cutO_le' T W) (resM P (cutO_le T W) s) := rfl

theorem toCut_injective {l l' : Γ(dual P, T)} (h : toCut l = toCut l') : l = l' :=
  dual_ext fun W hW s => by
    have := congrArg (resG Y (le_cutO hW le_rfl)) ((toCut_app l W s).symm.trans (h ▸ toCut_app l' W s))
    rwa [← dualApp_resM, ← dualApp_resM, resM_resM, resM_self] at this

def ofCut (φ : P ⟶ cut T) : Γ(dual P, T) :=
  dualMk (fun W h =>
    { toFun s := resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s))
      map_add' s t := by simp only [map_add (f := _)]
      map_smul' a s := by
        rw [Scheme.Modules.Hom.app_smul, cutEquiv_smul, map_mul, resG_resG, resG_self]; rfl })
    fun W W' h h' s => by
      change resG Y _ (cutEquiv T W' (φ.app W' (resM P h' s))) = resG Y h' (resG Y _ _)
      rw [app_resM, cutEquiv_res, resG_resG, resG_resG]

theorem dualApp_ofCut (φ : P ⟶ cut T) {W : Y.Opens} (h : W ≤ T) (s : Γ(P, W)) :
    dualApp (ofCut φ) h s = resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s)) := rfl

variable (f : Y ⟶ X)

def adj {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    (Scheme.Modules.pullback f).obj F ⟶ G :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).symm ψ

theorem adj_app {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G)
    {V : X.Opens} (e : T ≤ f ⁻¹ᵁ V) (s : Γ(F, V)) :
    (adj f ψ).app T (pullbackSections f F e s) = resM G e (ψ.app V s) := by
  refine (QCoh.hom_app_res (adj f ψ) e _).trans (congrArg (resM G e) ?_)
  have := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).apply_symm_apply ψ
  rw [Adjunction.homEquiv_unit] at this
  exact congr(($this).app V s)

theorem pull_ext {F : X.Modules} {G : Y.Modules} {φ φ' : (Scheme.Modules.pullback f).obj F ⟶ G}
    (h : ∀ (V : X.Opens) (s : Γ(F, V)), φ.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s) =
      φ'.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s)) : φ = φ' := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have e : pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s = _ := QCoh.res_self _ _ _
  exact (congrArg (φ.app _) e).symm.trans ((h V s).trans (congrArg (φ'.app _) e))

variable {F G : X.Modules} {V : X.Opens}

theorem dual_pull_ext (e : T ≤ f ⁻¹ᵁ V) {l l' : Γ(dual ((Scheme.Modules.pullback f).obj F), T)}
    (h : ∀ (W : X.Opens) (_ : W ≤ V) (S : Y.Opens) (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)),
      dualApp l hS (pullbackSections f F e' s) = dualApp l' hS (pullbackSections f F e' s)) :
    l = l' := by
  refine toCut_injective (pull_ext f fun W s => (cutEquiv T _).injective ?_)
  have e' : cutO T (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
    le_inf (cutO_le T (f ⁻¹ᵁ W)) ((cutO_le' T (f ⁻¹ᵁ W)).trans e)
  have : resM _ (cutO_le T (f ⁻¹ᵁ W)) (pullbackSections f F (le_refl (f ⁻¹ᵁ W)) s) =
      pullbackSections f F e' (resM F inf_le_left s) :=
    (QCoh.res_pullbackSections f F _ _ _).trans (QCoh.pullbackSections_res f F e' _ _).symm
  rw [toCut_app, toCut_app, this]
  exact h _ inf_le_right _ _ _ _

theorem cutO_le_inf (V W : X.Opens) : cutO (f ⁻¹ᵁ V) (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
  le_inf (cutO_le (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)) (cutO_le' (f ⁻¹ᵁ V) (f ⁻¹ᵁ W))

theorem appLE_resG {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ W) (a : Γ(X, V)) :
    f.appLE W T e (resG X h a) = f.appLE V T (e.trans (f.preimage_mono h)) a :=
  congr($(f.map_appLE e (homOfLE h).op) a)

theorem resG_appLE {S : Y.Opens} (h : S ≤ T) (e : T ≤ f ⁻¹ᵁ V) (a : Γ(X, V)) :
    resG Y h (f.appLE V T e a) = f.appLE V S (h.trans e) a :=
  congr($(f.appLE_map e (homOfLE h).op) a)

def formPush (l : Γ(dual F, V)) : F ⟶ (Scheme.Modules.pushforward f).obj (cut (f ⁻¹ᵁ V)) :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).symm (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
        (dualApp l inf_le_right (resM F inf_le_left s)))
      map_add' s t := by simp only [map_add (f := _)]; rfl
      map_smul' a s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).injective (by
        refine Eq.trans ?_ (cutEquiv_smul _ _ (f.app W a) _).symm
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul, map_mul, appLE_resG]
        rfl) })
    fun {W W'} h s => (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W')).injective (by
      change f.appLE (W' ⊓ V) _ _ (dualApp l _ (resM F _ (resM F h s))) =
        resG Y (cutO_mono _ (f.preimage_mono h)) (f.appLE (W ⊓ V) _ _ (dualApp l _ (resM F _ s)))
      rw [resG_appLE, ← appLE_resG f (inf_le_inf_right V h) (cutO_le_inf f V W'), ← dualApp_resM,
        resM_resM, resM_resM])

def pullForm (l : Γ(dual F, V)) : Γ(dual ((Scheme.Modules.pullback f).obj F), f ⁻¹ᵁ V) :=
  ofCut (adj f (formPush f l))

theorem dualApp_pullForm (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (hT : T ≤ f ⁻¹ᵁ V)
    (e : T ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp (pullForm f l) hT (pullbackSections f F e s) = f.appLE W T e (dualApp l h s) := by
  rw [pullForm, dualApp_ofCut, adj_app]
  change resG Y _ (resG Y (cutO_mono _ e) (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
    (dualApp l inf_le_right (resM F inf_le_left s)))) = _
  rw [resG_appLE, resG_appLE, dualApp_resM l h, appLE_resG]


variable (F) in
def pullFormHom :
    dual F ⟶ (Scheme.Modules.pushforward f).obj (dual ((Scheme.Modules.pullback f).obj F)) :=
  homOfLinear (fun V =>
    { toFun l := pullForm f l
      map_add' l l' := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = dualApp (pullForm f l) hS _ + dualApp (pullForm f l') hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_add,
          LinearMap.add_apply, map_add]
      map_smul' a l := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = resG Y hS (f.app V a) * dualApp (pullForm f l) hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_smul,
          LinearMap.smul_apply, smul_eq_mul, map_mul, appLE_resG]
        rfl })
    fun {V V'} hV l => dual_pull_ext f le_rfl fun W h S hS e s => by
      change dualApp (pullForm f (resM _ hV l)) hS _ =
        dualApp (pullForm f l) (hS.trans (f.preimage_mono hV)) _
      rw [dualApp_pullForm f _ h, dualApp_pullForm f _ (h.trans hV), dualApp_res]


variable (F) in
def theta : (Scheme.Modules.pullback f).obj (dual F) ⟶ dual ((Scheme.Modules.pullback f).obj F) :=
  adj f (pullFormHom f F)

theorem dualApp_theta (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ V)
    {S : Y.Opens} (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp ((theta f F).app T (pullbackSections f (dual F) e l)) hS (pullbackSections f F e' s) =
      f.appLE W S e' (dualApp l h s) := by
  rw [theta, adj_app]
  exact dualApp_pullForm f l h (hS.trans e) e' s

theorem isIso_theta {r : ℕ} (h : IsVB F r) : IsIso (theta f F) := by
  have := h.isQuasicoherent
  have := h.dual.isQuasicoherent
  refine isIso_of_frames (ι := Fin r) _ fun y => ?_
  obtain ⟨U, e, hx, he⟩ := h (f y)
  refine ⟨f ⁻¹ᵁ U, _, hx, he.dual.pullback f, ?_⟩
  have H (i : Fin r) : (theta f F).app _ (pullbackSections f (dual F) (le_refl (f ⁻¹ᵁ U))
      (he.coord i)) = (he.pullback f).coord i :=
    dual_pull_ext f le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta f _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact (he.pullback_basis_repr f hW e' s i).symm
  rw [funext H]
  exact (he.pullback f).dual

end GlobalTheory.DualPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasInfCharGL
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.IrrInfChar

theorem cap_commute_act' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ) (u : ℂ)
    (o : Op E a) : Commute (cap (a := a) τ u) (act o) := by
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

theorem exists_scalar {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {V : Submodule ℂ (Sm E a)}
    (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem exists_hasInfCharGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (τ : E →+* ℂ) : ∃ μ, HasInfCharGL V τ μ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := N) τ) (((N : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_scalar hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (fun o => cap_commute_act' τ u o)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (τ : E →+* ℂ), (∀ x : CuspSub E N, ∃ μ, x.HasInfChar τ μ) ∧ ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∃ μ, HasInfCharGL V τ μ := by
  intro E _ _ _ N τ
  refine ⟨fun x => ⟨(CG.mk x).infChar τ, ?_⟩, fun V hV => exists_hasInfCharGL hV τ⟩
  exact hasInfChar_infChar_of_commute E N (fun τ u o => cap_commute_act' τ u o) (CG.mk x) τ

end GlobalTheory.ResW.IrrInfChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPairSelfDualLatticeIsotropic
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HypPairLat

theorem form_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J (c • z) w = c * form σ J z w := by
  simp [form, smul_dotProduct]

theorem form_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J z (c • w) = σ c * form σ J z w := by
  have : (fun i => σ ((c • w) i)) = σ c • fun i => σ (w i) := by ext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_conj {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (z w : Fin n → E) :
    σ (form σ J z w) = form σ J w z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem isIntegral_sigma {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {e : E}
    (h : IsIntegral ℤ e) : IsIntegral ℤ (σ e) :=
  h.map (σ.toRingHom.toIntAlgHom)

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsHerm σ B r s →
    ∀ x : Fin n → E, x ≠ 0 → form σ Y.J x x = 0 →
    ∃ x' y : Fin n → E, form σ Y.J x' x' = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x' y = 1 ∧
      (∀ z ∈ Y.L, form σ Y.J z y • x' ∈ Y.L ∧ form σ Y.J z x' • y ∈ Y.L) ∧
      ∀ v : B.P, ((∀ c : E, c • x' ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • x' ∈ Y.L ∧ Valued.v (B.τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ Y.L ∧ Valued.v (B.τ v c) = 1) := by
  intro F E _ _ _ _ _ σ B hB n Y r s hY x hx0 hxx
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by haveI := hB.unram; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm hfu
  have hfg : Y.L.FG := hY.lat.fg
  obtain ⟨z0, hz0L, hz0⟩ := _root_.GlobalTheory.selfDual_pair_nondeg F E σ hσ n Y.J Y.L hfg hY.herm hY.dual x hx0
  let f : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ Y.J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun c a => by
        show form σ Y.J ((c : E) • a) x = (c : E) * form σ Y.J a x
        exact form_smul_left σ Y.J (c : E) a x }
  have hf : ∀ z, f z = form σ Y.J z x := fun z => rfl
  let I₀ : Submodule (𝓞 E) E := Y.L.map f
  have hI₀fg : I₀.FG := hfg.map f
  have hI₀ne : I₀ ≠ ⊥ := by
    intro h
    have : f z0 ∈ I₀ := Submodule.mem_map_of_mem hz0L
    rw [h, Submodule.mem_bot] at this
    exact hz0 this
  have hT4 := fun (v : B.P) (b : Bool) => _root_.GlobalTheory.adicEmbedding_integral_place F E v.1 (if b then (B.τ v).comp σ else B.τ v)
  choose hle Q hQmax hQ using hT4
  obtain ⟨s, hs0, hsI, hsQ⟩ := _root_.GlobalTheory.exists_scale_integral_not_le_maximal E I₀ hI₀fg hI₀ne (B.P × Bool) (fun p => Q p.1 p.2) (fun p => hQmax _ _)
  set x' : Fin n → E := σ s • x with hx'def
  have hfx' : ∀ z, form σ Y.J z x' = s * form σ Y.J z x := fun z => by
    rw [hx'def, form_smul_right, hσ]
  have hx'x' : form σ Y.J x' x' = 0 := by
    rw [hfx', hx'def, form_smul_left, hxx, mul_zero, mul_zero]
  obtain ⟨y₀, hy₀1, hy₀L⟩ := _root_.GlobalTheory.FormSection.exists_section F E σ n Y.J Y.L hfg x' ⟨z0, hz0L, by rw [hfx']; exact mul_ne_zero hs0 hz0⟩
  obtain ⟨y, hyy, hx'y, hL⟩ := _root_.GlobalTheory.TraceCorrection.exists_pair F E σ hσ n Y.J Y.L hY.herm hY.dual θ hθ x' y₀ hx'x' hy₀1 hy₀L
  have hint : ∀ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') := fun z hz => by
    rw [hfx']; exact hsI _ (Submodule.mem_map_of_mem hz)
  have hx'L : x' ∈ Y.L := (hY.dual x').2 fun w hw => by
    rw [← form_conj σ hσ Y.J hY.herm]; exact isIntegral_sigma σ (hint w hw)
  have hyx' : form σ Y.J y x' = 1 := by
    rw [← form_conj σ hσ Y.J hY.herm, hx'y, map_one]

  have hval : ∀ (v : B.P) (b : Bool) (e : E), IsIntegral ℤ e →
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) e) ≤ 1 := fun v b e he =>
    hle v b ⟨e, he⟩
  have hwit : ∀ (v : B.P) (b : Bool), ∃ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') ∧
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) (form σ Y.J z x')) = 1 := by
    intro v b
    obtain ⟨a, ha, o, ho, hoQ⟩ := hsQ (v, b)
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 ha
    refine ⟨z, hz, hint z hz, ?_⟩
    have h1 := hle v b o
    have h2 : ¬ Valued.v ((if b then (B.τ v).comp σ else B.τ v) (o : E)) < 1 := fun h => hoQ ((hQ v b o).2 h)
    rw [ho, hf, ← hfx'] at h1 h2
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨x', y, hx'x', hyy, hx'y, hL, fun v => ⟨⟨fun c hc => ?_, 1, by rw [one_smul]; exact hx'L, by simp⟩,
    ⟨fun c hc => ?_, ?_⟩⟩⟩
  · obtain ⟨z, hz, -, hz1⟩ := hwit v true
    have hi : IsIntegral ℤ (form σ Y.J (c • x') z) := (hY.dual _).1 hc z hz
    rw [form_smul_left, ← form_conj σ hσ Y.J hY.herm z x'] at hi
    have := hval v false _ hi
    simp only [Bool.false_eq_true, ↓reduceIte, map_mul] at this
    simp only [↓reduceIte, AlgHom.comp_apply] at hz1
    rw [hz1, mul_one] at this
    exact this
  · have hi := hint _ hc
    rw [form_smul_left, hyx', mul_one] at hi
    simpa using hval v false c hi
  · obtain ⟨z, hz, -, hz1⟩ := hwit v false
    exact ⟨form σ Y.J z x', (hL z hz).2, by simpa using hz1⟩

end GlobalTheory.HypPairLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem dchi_absC_one_finrank (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : ℂ) :
    dchi (GlobalTheory.CuspRep.Model.absC E s) 1 = s * (Module.finrank ℚ E : ℂ) := by
  let A : Cinf E →L[ℝ] ℂ :=
    s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (GlobalTheory.CuspRep.Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [GlobalTheory.CuspRep.Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  have h2 : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  rw [h, h2]
  simp [A, mul_comm]

theorem exists_abs_cpow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : ℂ), ∃ χ : HChar E, (∀ (a : ℕ) (φ : Sm E a), zc E a (mulChi a χ φ) = mulChi a χ (zc E a φ + (a * (Module.finrank ℚ E : ℂ) * z) • φ)) ∧ (∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ∧ (∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ = ‖(((nu E z.re).1 x : ℂˣ) : ℂ)‖) ∧ (z.im = 0 → χ = nu E z.re) := by
  intro E _ _ _ z
  refine ⟨GlobalTheory.CuspRep.Model.absC E z, fun a φ => ?_, fun v => ⟨fun x hx => Units.ext ?_, ?_⟩, fun x => ?_, fun hz => ?_⟩
  · unfold zc
    rw [lie_mulChi]
    have e : (Matrix.of (fun i j : Fin a => if i = j then (1 : Cinf E) else 0)).trace = (a : ℝ) • (1 : Cinf E) := by
      simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
    rw [e, map_smul, dchi_absC_one_finrank]
    congr 3
    simp only [Complex.real_smul, Complex.ofReal_natCast]; ring
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v x)) = 1
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v x 0 (by simpa [IsUnitAt] using hx)]; simp
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v (atFin v (unif v)))) = _
    have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
      ← Complex.natCast_log]
    congr 1; push_cast; ring
  · change ‖Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖ =
      ‖Complex.exp ((z.re : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖
    rw [Complex.norm_exp, Complex.norm_exp]; simp
  · have e : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz)
    conv_lhs => rw [e]
    rfl

end GlobalTheory.ResW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_conj_trivialization_at_place_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (g : G.GAf) (c Y : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * Y * ((c⁻¹ : G.Cˣ) : G.C) → ∀ w : AwayP p,
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
        inC G (w.1.adicCompletion ℚ) (β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  first | (exact @GlobalTheory.FinClsLoc.glueL_main) | (exact GlobalTheory.FinClsLoc.glueL_main) | (intros; apply GlobalTheory.FinClsLoc.glueL_main  <;> assumption)
end

