module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncIso

theorem mem_vanishingIdeal_ideal_iff {X : Scheme.{0}} (Z : Closeds X) (U : X.affineOpens) (s : Γ(X, U.1)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U ↔
      ∀ x ∈ (U.1 : Set X), x ∈ (Z : Set X) → x ∉ X.basicOpen s := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · rintro h x hxU hxZ hxs
    rw [← U.2.range_fromSpec] at hxU
    obtain ⟨p, rfl⟩ := hxU
    have hp : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := hxs
    rw [U.2.fromSpec_preimage_basicOpen] at hp
    exact hp (h p hxZ)
  · intro h p hpZ
    by_contra hs
    have hp : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [U.2.fromSpec_preimage_basicOpen]; exact hs
    have hpU : U.2.fromSpec p ∈ (U.1 : Set X) := by
      rw [← U.2.range_fromSpec]; exact ⟨p, rfl⟩
    exact h _ hpU hpZ hp

theorem rsp_ringEquiv {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    {n : ℕ} {x : Fin n → R} (h : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R n x) : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp S n (fun i => e (x i)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have hr : Set.range (fun i => e (x i)) = e '' Set.range x := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Ideal.map_span, h1]
  ext y
  rw [Ideal.mem_map_of_equiv, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩ hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hz ((isUnit_map_iff e z).1 hu)
  · intro hy
    refine ⟨e.symm y, (IsLocalRing.mem_maximalIdeal _).2 fun hu => hy ?_, e.apply_symm_apply y⟩
    simpa using (isUnit_map_iff e (e.symm y)).2 hu

theorem snc_vanishingIdeal_of_isIso {A B : Scheme.{0}} (f : A ⟶ B) [IsIso f] (Z : Closeds B) (Z' : Closeds A)
    (hZ : ∀ a : A, a ∈ Z' ↔ f a ∈ Z) (h : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z)) :
    ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z') := by
  intro a
  obtain ⟨hreg, U, hU, n, g, J, hrsp, hid⟩ := h (f a)
  let e : B.presheaf.stalk (f a) ≃+* A.presheaf.stalk a := (asIso (f.stalkMap a)).commRingCatIsoToRingEquiv
  have he : ∀ t, e t = f.stalkMap a t := fun _ => rfl
  let U' : A.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have hU' : a ∈ U'.1 := hU
  refine ⟨IsRegularLocalRing.of_ringEquiv e, U', hU', n, fun i => f.app U.1 (g i), J, ?_, ?_⟩
  · have hg : ∀ i, A.presheaf.germ U'.1 a hU' (f.app U.1 (g i)) = e (B.presheaf.germ U.1 (f a) hU (g i)) := by
      intro i
      rw [he, Scheme.Hom.germ_stalkMap_apply]
    simp only [hg]
    exact rsp_ringEquiv e hrsp
  · let φ : Γ(B, U.1) ≃+* Γ(A, U'.1) := (asIso (f.app U.1)).commRingCatIsoToRingEquiv
    have hφ : ∀ t, φ t = f.app U.1 t := fun _ => rfl
    ext t
    obtain ⟨s, rfl⟩ : ∃ s, φ s = t := φ.surjective t
    have key : φ s ∈ (Scheme.IdealSheafData.vanishingIdeal Z').ideal U' ↔
        s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U := by
      rw [mem_vanishingIdeal_ideal_iff, mem_vanishingIdeal_ideal_iff, hφ, ← Scheme.preimage_basicOpen]
      constructor
      · intro H b hbU hbZ hbs
        obtain ⟨a', rfl⟩ : ∃ a', f a' = b := ⟨(inv f) b, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
        exact H a' hbU ((hZ a').2 hbZ) hbs
      · intro H a' ha'U ha'Z ha's
        exact H (f a') ha'U ((hZ a').1 ha'Z) ha's
    rw [key, hid, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    have hp : (∏ i ∈ J, f.app U.1 (g i)) = φ (∏ i ∈ J, g i) := by
      rw [map_prod]; rfl
    rw [hp, map_dvd_iff]

end GlobalTheory.SncIso

namespace GlobalTheory.VarFlag

open GlobalTheory.Toroidal (gen genι genBd genBdIdeal mem_genBd)

theorem snc_genBdIdeal_of_snc_boundary {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} :
    ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.LogKS.boundary Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.Toroidal.genBdIdeal Y) := by
  intro h
  refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y) (GlobalTheory.LogKS.interior Y).compl (genBd Y) ?_ h
  intro a
  have hinj : Function.Injective (genι Y) := (genι Y).isOpenEmbedding.injective
  rw [mem_genBd]
  show a ∉ Set.range Y.jQ ↔ genι Y a ∉ Set.range Y.j
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Model.j, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, hinj ?_⟩
    rw [← hx, Model.j, Scheme.Hom.comp_apply]

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanIInterSubmodulesOfFlatBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

noncomputable section

namespace GlobalTheory.Desc.FlatInter

theorem exists_fin_sum {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M ⊗[R] N) : ∃ (n : ℕ) (u : Fin n → M) (r : Fin n → N), x = ∑ i, u i ⊗ₜ[R] r i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul m n => exact ⟨1, fun _ => m, fun _ => n, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, u, r, rfl⟩ := hx
    obtain ⟨m, u', r', rfl⟩ := hy
    exact ⟨n + m, Fin.append u u', Fin.append r r', by simp [Fin.sum_univ_add]⟩

theorem mem_range_iInf {R K R₁ : Type} [CommRing R] [AddCommGroup K] [Module R K] [AddCommGroup R₁] [Module R R₁]
    [Module.Flat R R₁] {J : Type} [Finite J] (N : J → Submodule R K) (T : K ⊗[R] R₁)
    (hT : ∀ j, T ∈ LinearMap.range ((N j).subtype.rTensor R₁)) :
    T ∈ LinearMap.range ((⨅ j, N j).subtype.rTensor R₁) := by
  classical
  have := Fintype.ofFinite J
  let π : K →ₗ[R] ∀ j, K ⧸ N j := LinearMap.pi fun j => (N j).mkQ
  have hex : Function.Exact (⨅ j, N j).subtype π := by
    rw [LinearMap.exact_iff]
    simp [π, LinearMap.ker_pi]
  have hex' := Module.Flat.rTensor_exact R₁ hex
  rw [← LinearMap.exact_iff.mp hex']
  rw [LinearMap.mem_ker]
  let e := TensorProduct.piLeft R R₁ (fun j => K ⧸ N j)
  apply e.injective
  rw [map_zero]
  funext j
  have hj : LinearMap.proj j ∘ₗ e.toLinearMap ∘ₗ π.rTensor R₁ = (N j).mkQ.rTensor R₁ := by
    ext x r
    simp [π, e]
  have := congrArg (fun f => f T) hj
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_proj,
    Function.eval] at this
  rw [this, Pi.zero_apply, ← LinearMap.mem_ker, rTensor_mkQ]
  exact hT j

def tensorMap {R R₁ K L : Type} [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K]
    (θ : K →+* L) (c : R₁ →+* L) (hc : ∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) :
    K ⊗[R] R₁ →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun r => c r * θ u) (fun a b => by simp [add_mul]))
      (fun a b => by ext r; simp [mul_add]))
    (fun a u r => by
      simp only [AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, hc]
      ring)

theorem tensorMap_tmul {R R₁ K L : Type} [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁]
    [Algebra R K] (θ : K →+* L) (c : R₁ →+* L) (hc : ∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a))
    (u : K) (r : R₁) : tensorMap θ c hc (u ⊗ₜ[R] r) = c r * θ u := rfl

end GlobalTheory.Desc.FlatInter


open GlobalTheory.Desc.FlatInter in
theorem GlobalTheory.Desc.spanBy_iInter_of_flat : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) → (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → ∀ (J : Type) [Finite J] [Nonempty J] (N : J → Submodule R K), spanBy c (θ '' ⋂ j, (N j : Set K)) = ⋂ j, spanBy c (θ '' (N j : Set K)) := by
  intro R R₁ K L _ _ _ _ _ _ _ θ c hc hinj J _ _ N
  let Φ := tensorMap θ c hc
  have hΦ : ∀ x, Φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨n, u, r, rfl⟩ := exists_fin_sum x
    apply hinj n u r
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Φ, map_sum, tensorMap_tmul] using hx
  ext v
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    refine Set.mem_iInter.2 fun j => ⟨n, r, t, fun i => Set.image_mono (Set.iInter_subset _ j) (ht i), rfl⟩
  · intro hv
    have key : ∀ j, ∃ T ∈ LinearMap.range ((N j).subtype.rTensor R₁), Φ T = v := by
      intro j
      obtain ⟨n, r, t, ht, rfl⟩ := Set.mem_iInter.1 hv j
      choose u hu hut using ht
      refine ⟨(N j).subtype.rTensor R₁ (∑ i, (⟨u i, hu i⟩ : N j) ⊗ₜ[R] r i), LinearMap.mem_range_self _ _, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Φ, map_sum, tensorMap_tmul, hut]
    choose T hT hTv using key
    obtain ⟨j₀⟩ := ‹Nonempty J›
    have heq : ∀ j, T j = T j₀ := fun j => by
      have := hΦ (T j - T j₀) (by rw [map_sub, hTv, hTv, sub_self])
      exact sub_eq_zero.1 this
    obtain ⟨y, hy⟩ := mem_range_iInf N (T j₀) fun j => heq j ▸ hT j
    obtain ⟨n, w, s, rfl⟩ := exists_fin_sum y
    refine ⟨n, s, fun i => θ (w i), fun i => ⟨w i, ?_, rfl⟩, ?_⟩
    · exact Set.mem_iInter.2 fun j => (Submodule.mem_iInf N).1 (w i).2 j
    · rw [← hTv j₀, ← hy]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Φ, map_sum, tensorMap_tmul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInterOfFlatLinearlyDisjoint
section
open GlobalTheory.Desc

open TensorProduct

namespace GlobalTheory.FlatSpanInter

theorem spanBy_algebraMap_eq {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] [Algebra R₁ F₁] (T : Set F₁) :
    spanBy (algebraMap R₁ F₁) T = (Submodule.span R₁ T : Set F₁) := by
  ext v
  simp only [SetLike.mem_coe, Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, by simp [Algebra.smul_def]⟩
  · rintro ⟨n, r, t, rfl⟩
    exact ⟨n, r, fun i => t i, fun i => (t i).2, by simp [Algebra.smul_def]⟩

variable {R R₁ F F₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [CommRing F₁]
  [Algebra R R₁] [Algebra R F] [Algebra R₁ F₁] [Algebra R F₁] [IsScalarTower R R₁ F₁]

theorem smul_injective_tensor (hc₀ : Function.Injective (algebraMap R F)) {d : R} (hd : d ≠ 0)
    (x : R₁ ⊗[R] F) (hx : d • x = 0) : x = 0 := by
  set u : F := (algebraMap R F d)⁻¹
  have hu : u * algebraMap R F d = 1 :=
    inv_mul_cancel₀ (fun h => hd (hc₀ (by rw [h, map_zero])))
  have key : ∀ z : R₁ ⊗[R] F, LinearMap.lTensor R₁ (LinearMap.mulLeft R u) (d • z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r f =>
      rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, Algebra.smul_def,
        ← mul_assoc, hu, one_mul]
    | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb]
  rw [← key x, hx, map_zero]

theorem free_injective (θ : F →ₐ[R] F₁)
    (hLD : LinDisj (algebraMap R F) (algebraMap R₁ F₁) (θ : F →+* F₁))
    {ι : Type} [Fintype ι] (v : ι → F) (hli : LinearIndependent R v) :
    Function.Injective ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  set bB := Module.Basis.span hli
  set bb := Algebra.TensorProduct.basis R₁ bB
  have hval : ∀ j, ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) (bb j) = θ (v j) := by
    intro j
    simp [bb, bB, Algebra.TensorProduct.basis_apply, Module.Basis.span_apply, LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]
  have e1 : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) y =
        ∑ j, algebraMap R₁ F₁ (bb.repr y j) * θ (v j) := by
    conv_lhs => rw [← bb.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hval, Algebra.smul_def]
  rw [hy] at e1
  set e := (Fintype.equivFin ι).symm
  have h0 := hLD _ (v ∘ e) (by
      intro r hr
      funext i
      exact Fintype.linearIndependent_iff.1 (hli.comp e e.injective) r
        (by simpa [Algebra.smul_def] using hr) i)
    (fun i => bb.repr y (e i)) (by
      rw [e1, ← Equiv.sum_comp e]
      rfl)
  have hr : bb.repr y = 0 := by
    ext j
    simpa using congrFun h0 (e.symm j)
  exact bb.repr.map_eq_zero_iff.1 hr

theorem liftBaseChange_injective (hc₀ : Function.Injective (algebraMap R F)) (θ : F →ₐ[R] F₁)
    (hLD : LinDisj (algebraMap R F) (algebraMap R₁ F₁) (θ : F →+* F₁)) :
    Function.Injective (LinearMap.liftBaseChange R₁ θ.toLinearMap) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  set g : S → F := fun i => (i : R₁ × F).2
  obtain ⟨s, hli, hmax⟩ := exists_maximal_linearIndepOn R g
  have ha : ∀ i, ∃ a : R, a ≠ 0 ∧ a • g i ∈ Submodule.span R (g '' s) := by
    intro i
    by_cases hi : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩
    · exact hmax i hi
  choose a ha0 ha using ha
  set d := ∏ i, a i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)
  have hdg : ∀ i, d • g i ∈ Submodule.span R (Set.range fun j : s => g j) := by
    intro i
    rw [← Set.image_eq_range]
    obtain ⟨e, he⟩ : a i ∣ d := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    rw [he, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (ha i)
  haveI : Fintype s := Fintype.ofFinite s
  set B := Submodule.span R (Set.range fun j : s => g j)
  set y : R₁ ⊗[R] B := ∑ i : S, (i : R₁ × F).1 ⊗ₜ ⟨d • g i, hdg i⟩
  have hy : B.subtype.baseChange R₁ y = d • ∑ i ∈ S, i.1 ⊗ₜ i.2 := by
    rw [Finset.smul_sum, ← Finset.sum_coe_sort S]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.tmul_smul, g]
  have hz : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ (B.subtype.baseChange R₁)) y = 0 := by
    rw [LinearMap.comp_apply, hy, LinearMap.map_smul_of_tower, hx, smul_zero]
  have hy0 : y = 0 := free_injective θ hLD (fun j : s => g j) hli (by rw [hz, map_zero])
  exact smul_injective_tensor hc₀ hd _ (by rw [← hy, hy0, map_zero])

theorem spanBy_image_eq_map (θ : F →ₐ[R] F₁) (P : Submodule R F) :
    spanBy (algebraMap R₁ F₁) (θ '' P) =
      ((P.baseChange R₁).map (LinearMap.liftBaseChange R₁ θ.toLinearMap) : Set F₁) := by
  rw [spanBy_algebraMap_eq, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  congr 2
  ext p
  simp [LinearMap.liftBaseChange_tmul]

end GlobalTheory.FlatSpanInter

theorem GlobalTheory.Desc.spanBy_image_inter : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [Field F₁]
    (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁), ρ.Flat → Function.Injective c₀ →
    θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (M N : Set F), (0 : F) ∈ M → (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) →
    (∀ r, ∀ a ∈ M, c₀ r * a ∈ M) → (0 : F) ∈ N → (∀ a ∈ N, ∀ b ∈ N, a + b ∈ N) → (∀ r, ∀ a ∈ N, c₀ r * a ∈ N) →
    spanBy c₁ (θ '' (M ∩ N)) = spanBy c₁ (θ '' M) ∩ spanBy c₁ (θ '' N) := by
  intro R R₁ F F₁ _ _ _ _ _ ρ c₀ c₁ θ hρ hc₀ hcomp hLD M N hM0 hMa hMs hN0 hNa hNs
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R F := c₀.toAlgebra
  letI : Algebra R₁ F₁ := c₁.toAlgebra
  letI : Algebra R F₁ := (c₁.comp ρ).toAlgebra
  haveI : IsScalarTower R R₁ F₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat R R₁ := hρ
  let θa : F →ₐ[R] F₁ := { θ with commutes' := fun r => RingHom.congr_fun hcomp r }
  let MS : Submodule R F :=
    { carrier := M, add_mem' := fun ha hb => hMa _ ha _ hb, zero_mem' := hM0,
      smul_mem' := fun r a ha => hMs r a ha }
  let NS : Submodule R F :=
    { carrier := N, add_mem' := fun ha hb => hNa _ ha _ hb, zero_mem' := hN0,
      smul_mem' := fun r a ha => hNs r a ha }
  have hinj := GlobalTheory.FlatSpanInter.liftBaseChange_injective (R₁ := R₁) hc₀ θa hLD
  have kI : spanBy c₁ (θ '' (M ∩ N)) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa (MS ⊓ NS)
  have kM : spanBy c₁ (θ '' M) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa MS
  have kN : spanBy c₁ (θ '' N) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa NS
  rw [kI, kM, kN, GlobalTheory.baseChange_inf, Submodule.map_inf _ hinj, Submodule.coe_inf]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.AlgConn

theorem connectedSpace_specialFibre_of_morphisms : GlobalTheory.Published.FormalAlgebraisation.Morphisms →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)),
      IsProper f → ConnectedSpace ↑Y → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := by
  intro H O _ _ _ hI Y f hP hY
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hT : Set.range (specialι f) = f ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [range_residue] at h
    exact h
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hTn : ∀ n, Set.range (thickι f n) = f ⁻¹' {IsLocalRing.closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (thickQ O n)))
    rw [range_thickQ] at h
    exact h
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hne : ∃ y : Y, f y = IsLocalRing.closedPoint O := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hsp : f y ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (f y).2.ne_top)
    exact hsp.mem_closed hc ⟨y, rfl⟩
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  obtain ⟨y₀, hy₀⟩ := hne
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hy₀' : y₀ ∈ Set.range (specialι f) := by rw [hT]; exact hy₀
  obtain ⟨z₀, -⟩ := hy₀'
  haveI : Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := ⟨z₀⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))))
  have hcl : Topology.IsClosedEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f).isClosedEmbedding
  refine { toPreconnectedSpace := preconnectedSpace_iff_clopen.2 fun U hU => ?_, toNonempty := ‹_› }
  by_contra hcon
  push_neg at hcon
  obtain ⟨hU0, hU1⟩ := hcon
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra h
    push_neg at h
    exact hU1 (Set.eq_univ_of_forall h)
  let A := GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f '' U
  let B := GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f '' Uᶜ
  have hA : IsClosed A := hcl.isClosedMap _ hU.1
  have hB : IsClosed B := hcl.isClosedMap _ hU.2.isClosed_compl
  have hpt : ∀ n (z : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f), ∃ x, GlobalTheory.SpecialConn.thickι f n x =
      GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f z := fun n z => by
    have : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f z ∈ Set.range (GlobalTheory.SpecialConn.thickι f n) := by
      rw [hTn, ← hT]; exact ⟨z, rfl⟩
    exact this
  have hAB : ∀ n, (GlobalTheory.SpecialConn.thickι f n ⁻¹' A)ᶜ = GlobalTheory.SpecialConn.thickι f n ⁻¹' B := by
    intro n
    ext x
    obtain ⟨z, hz⟩ : GlobalTheory.SpecialConn.thickι f n x ∈ Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) := by
      rw [hT, ← hTn n]; exact ⟨x, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, A, B, Set.mem_image]
    constructor
    · intro h
      exact ⟨z, fun hzU => h ⟨z, hzU, hz⟩, hz⟩
    · rintro ⟨w, hw, hw'⟩ ⟨w', hw'U, hw''⟩
      exact hw (hcl.injective (hw''.trans hw'.symm) ▸ hw'U)
  have hclo : ∀ n, IsClopen (GlobalTheory.SpecialConn.thickι f n ⁻¹' A) := fun n =>
    ⟨hA.preimage (GlobalTheory.SpecialConn.thickι f n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (GlobalTheory.SpecialConn.thickι f n).continuous⟩
  choose h hhp hhU using fun n => _root_.GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen O (GlobalTheory.SpecialConn.thickFib f n)
    (GlobalTheory.SpecialConn.thickι f n ≫ f) _ (hclo n)
  haveI : IsProper (Over.mk f).hom := hP
  haveI : IsProper (Over.mk (twoπ O)).hom := isProper_twoπ O
  have hc : ∀ n, GlobalTheory.SpecialConn.thickTr f n ≫ h (n + 1) = h n := by
    intro n
    refine GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq O _ _ _ ?_ ?_
    · rw [Category.assoc, hhp, hhp, ← Category.assoc, GlobalTheory.SpecialConn.thickTr_ι]
    · refine TopologicalSpace.Opens.ext ?_
      rw [hhU n, Scheme.Hom.comp_preimage]
      change GlobalTheory.SpecialConn.thickTr f n ⁻¹' ((h (n + 1) ⁻¹ᵁ _ : (GlobalTheory.SpecialConn.thickFib f (n+1)).Opens) : Set _) = _
      rw [hhU (n + 1), ← Set.preimage_comp, ← GlobalTheory.SpecialConn.thickTr_ι f n]
      rfl
  obtain ⟨g, hg, -⟩ := GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick H hI (Over.mk f)
    (Over.mk (twoπ O)) h (fun n => hhp n) hc
  have hW : IsClopen ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) :=
    (isClopen_basicOpen_specProdSelfFirstIdempotent O).preimage g.left.continuous
  have h0 : GlobalTheory.SpecialConn.thickι f 0 ⁻¹' ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) =
      GlobalTheory.SpecialConn.thickι f 0 ⁻¹' A := by
    rw [← hhU 0, ← hg 0]
    rfl
  obtain ⟨x, hx⟩ := hpt 0 u
  obtain ⟨x', hx'⟩ := hpt 0 u'
  rcases isClopen_iff.1 hW with hW0 | hW1
  · have hxA : x ∈ GlobalTheory.SpecialConn.thickι f 0 ⁻¹' A := ⟨u, hu, hx.symm⟩
    rw [← h0, hW0] at hxA
    simp at hxA
  · have hxA : x' ∈ GlobalTheory.SpecialConn.thickι f 0 ⁻¹'
        ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) := by
      rw [hW1]; trivial
    rw [h0] at hxA
    obtain ⟨w, hw, hw'⟩ := hxA
    exact hu' (hcl.injective (hw'.trans hx') ▸ hw)

end GlobalTheory.AlgConn
end
end

