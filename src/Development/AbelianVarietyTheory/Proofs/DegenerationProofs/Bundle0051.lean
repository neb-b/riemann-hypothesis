module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0047
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDualBundleGeneratorsAllThetaTests
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

section Specialise

variable {o Ω K J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field K] [Fintype J]

theorem map_dotProduct_of_mem {B : Subalgebra o Ω} {f : Ω → K} (φ : B →+* K) (hf : ∀ x : B, φ x = f x)
    {u v : J → Ω} (hu : ∀ j, u j ∈ B) (hv : ∀ j, v j ∈ B) :
    f (u ⬝ᵥ v) = (fun j => f (u j)) ⬝ᵥ fun j => f (v j) := by
  have h : u ⬝ᵥ v = ((∑ j, (⟨u j, hu j⟩ : B) * ⟨v j, hv j⟩ : B) : Ω) := by
    simp [dotProduct]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, ← hf, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hf, hf]

theorem dotProduct_mem_of_mem_span {σ : Type} [SetLike σ K] [SubringClass σ K] (O : σ) {s : Set (J → K)} {w v : J → K}
    (hs : ∀ x ∈ s, w ⬝ᵥ x ∈ O) (hv : v ∈ Submodule.span O s) : w ⬝ᵥ v ∈ O := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : w ⬝ᵥ (c • x) = (c : K) * (w ⬝ᵥ x) := dotProduct_smul (c : K) w x
    rw [this]
    exact mul_mem c.2 hx


omit [Fintype J] in
theorem map_mem_span_of_mem_span {A B : Subalgebra o Ω} (hAB : A ≤ B) {f : Ω → K} (φ : B →+* K)
    (hf : ∀ x : B, φ x = f x) (O : ValuationSubring K) (hO : ∀ x ∈ A, f x ∈ O) {I : Type} {g : I → J → Ω}
    (hg : ∀ k j, g k j ∈ B) {v : J → Ω} (hv : v ∈ Submodule.span A (Set.range g)) :
    (∀ j, v j ∈ B) ∧ (fun j => f (v j)) ∈ Submodule.span O (Set.range fun k j => f (g k j)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨hg k, Submodule.subset_span ⟨k, rfl⟩⟩
  | zero =>
    refine ⟨fun _ => zero_mem B, ?_⟩
    have h0 : f 0 = 0 := (hf 0).symm.trans (map_zero φ)
    have : (fun j => f ((0 : J → Ω) j)) = 0 := funext fun _ => h0
    rw [this]
    exact zero_mem _
  | add x y _ _ hx hy =>
    refine ⟨fun j => add_mem (hx.1 j) (hy.1 j), ?_⟩
    have : (fun j => f ((x + y) j)) = (fun j => f (x j)) + fun j => f (y j) := funext fun j =>
      (hf (⟨_, hx.1 j⟩ + ⟨_, hy.1 j⟩)).symm.trans (by rw [map_add (f := _), hf, hf]; rfl)
    rw [this]
    exact add_mem hx.2 hy.2
  | smul c x _ hx =>
    refine ⟨fun j => mul_mem (hAB c.2) (hx.1 j), ?_⟩
    have : (fun j => f ((c • x) j)) = (⟨f c, hO c c.2⟩ : O) • fun j => f (x j) := funext fun j =>
      (hf (⟨_, hAB c.2⟩ * ⟨_, hx.1 j⟩)).symm.trans (by rw [map_mul, hf, hf]; rfl)
    rw [this]
    exact Submodule.smul_mem _ _ hx.2

theorem mem_span_map_iff_forall_dotProduct_mem [DecidableEq J] {A B : Subalgebra o Ω} (hAB : A ≤ B) {f : Ω → K}
    (φ : B →+* K) (hf : ∀ x : B, φ x = f x) (O : ValuationSubring K) (hO : ∀ x ∈ A, f x ∈ O) {I : Type}
    {g : I → J → Ω} (hg : ∀ k j, g k j ∈ B) (b : Matrix J J Ω)
    (hb : Submodule.span B (Set.range b) = Submodule.span B (Set.range fun i => Pi.single i (1 : Ω)))
    (H : ∀ w : J → Ω, w ∈ Submodule.span A (Set.range g) ↔ ∀ v ∈ Submodule.span A (Set.range b), w ⬝ᵥ v ∈ A)
    (w : J → K) :
    w ∈ Submodule.span O (Set.range fun k j => f (g k j)) ↔
      ∀ v ∈ Submodule.span O ((fun (v : J → Ω) j => f (v j)) '' (Submodule.span A (Set.range b))), w ⬝ᵥ v ∈ O := by
  have hbB : ∀ i j, b i j ∈ B := fun i j => by
    have h : b i ∈ Submodule.span B (Set.range fun i => (Pi.single i (1 : Ω) : J → Ω)) :=
      hb ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
    rw [← hc]
    simp [Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def]
  constructor
  · intro hw v hv
    refine dotProduct_mem_of_mem_span O ?_ hv
    rintro _ ⟨x, hx, rfl⟩
    rw [dotProduct_comm]
    refine dotProduct_mem_of_mem_span O ?_ hw
    rintro _ ⟨k, rfl⟩
    rw [dotProduct_comm, ← map_dotProduct_of_mem φ hf (hg k) (map_mem_span_of_mem_span hAB φ hf O hO hbB hx).1]
    exact hO _ ((H _).1 (Submodule.subset_span ⟨k, rfl⟩) x hx)
  · intro hw
    have h1 : ∀ i, ∃ c : J → B, ∑ l, HSMul.hSMul (c l) (b l) = (Pi.single i 1 : J → Ω) := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
    choose c hc using h1
    let d : Matrix J J Ω := Matrix.of fun i l => (c i l : Ω)
    have hd : d * b = 1 := by
      ext i j
      have := congrFun (hc i) j
      simpa [Matrix.mul_apply, d, Finset.sum_apply, Subalgebra.smul_def, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    have hd' : b * d = 1 := mul_eq_one_comm.1 hd
    have h2 : ∀ i, (fun j => d j i) ∈ Submodule.span A (Set.range g) := fun i => (H _).2 fun v hv => by
      refine dotProduct_mem_of_mem_span A ?_ hv
      rintro _ ⟨l, rfl⟩
      have : (fun j => d j i) ⬝ᵥ b l = (b * d) l i := dotProduct_comm _ _
      rw [this, hd', Matrix.one_apply]
      split_ifs
      exacts [one_mem A, zero_mem A]
    have h3 : ∀ i, w ⬝ᵥ (fun j => f (b i j)) ∈ O := fun i =>
      hw _ (Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩)
    have h4 : ∀ j l, ∑ i, f (d j i) * f (b i l) = if j = l then 1 else 0 := fun j l => by
      have h := map_dotProduct_of_mem φ hf (u := d j) (v := fun i => b i l) (fun i => (c j i).2) (fun i => hbB i l)
      have h' : d j ⬝ᵥ (fun i => b i l) = (d * b) j l := rfl
      rw [h', hd, Matrix.one_apply] at h
      refine h.symm.trans ?_
      split_ifs
      exacts [(hf 1).symm.trans (map_one φ), (hf 0).symm.trans (map_zero φ)]
    have h5 : w = ∑ i, (⟨_, h3 i⟩ : O) • fun j => f (d j i) := by
      funext j
      have : ∀ i, ((⟨_, h3 i⟩ : O) • fun j => f (d j i)) j = ∑ l, w l * (f (d j i) * f (b i l)) := fun i => by
        show (w ⬝ᵥ (fun j => f (b i j))) * f (d j i) = _
        rw [dotProduct, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [Finset.sum_apply, Finset.sum_congr rfl fun i _ => this i, Finset.sum_comm]
      simp only [← Finset.mul_sum, h4]
      simp
    rw [h5]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (map_mem_span_of_mem_span hAB φ hf O hO hg (h2 i)).2


omit [Fintype J] in
theorem mem_span_iff_div_mem_span (O : ValuationSubring K) {I : Type} (G : I → J → K) {u : K} (hu : u ≠ 0)
    (w : J → K) :
    w ∈ Submodule.span O (Set.range G) ↔ u⁻¹ • w ∈ Submodule.span O (Set.range fun k j => G k j / u) := by
  have key : ∀ (G : I → J → K) (s : K) (w : J → K), w ∈ Submodule.span O (Set.range G) →
      s • w ∈ Submodule.span O (Set.range fun k => s • G k) := fun G s w hw => by
    have := Submodule.mem_map_of_mem (f := (LinearMap.lsmul K (J → K) s).restrictScalars O) hw
    rwa [Submodule.map_span, ← Set.range_comp] at this
  have e : (fun k j => G k j / u) = fun k => u⁻¹ • G k := by
    funext k j
    simp [div_eq_inv_mul]
  rw [e]
  refine ⟨key G _ w, fun h => ?_⟩
  simpa [smul_smul, hu] using key _ u _ h

end Specialise

theorem exists_generators_at_all_tests : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG₀ : Fin n → S.J → S.R), S.Over₀ M U₀ → IsAffineOpen U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → S.IsEE M U₀ EE → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => (GG₀ k j : Ω) / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ (R' : Subalgebra o Ω) (hR : S.R ≤ R') (GG : Fin n → S.J → R'), R'.FG ∧ (∀ k j, (GG k j : Ω) = GG₀ k j) ∧ (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) := by
  intro o Ω _ _ _ _ S M U₀ EE n a GG₀ hO hU hsupp hEE hgen
  refine ⟨M.ringOn U₀, hO.le, fun k j => ⟨GG₀ k j, hO.le (GG₀ k j).2⟩, RatModel.fg_ringOn hU hO.ne,
    fun _ _ => rfl, fun p _ y' τ hy' w => ?_⟩
  obtain ⟨z, y, hz, hv⟩ := RatModel.exists_cen_of_ringHom o Ω M U₀ (projProper _ _ _ hO.proj) hU hO.ne p y' hy'
  have hAt : S.At M y (y'.comp (Subalgebra.inclusion hO.le).toRingHom) := fun r => hv ⟨r, hO.le r.2⟩
  obtain ⟨x₀, hx₀⟩ := hO.div z
  have hδ := ((hsupp z p y _ τ hz hAt).1 x₀).1 hx₀
  obtain ⟨V, b, hzV, -, hb⟩ := EE.loc z
  let ξ : M.Z := (gPt p ≫ y) (IsLocalRing.closedPoint _)
  have hξ : ξ ⤳ z := RatModel.gPt_specializes hz.1 _
  have hξU : ξ ∈ U₀ := hz.2 ⟨_, rfl⟩
  have hle : M.ringOn U₀ ≤ M.O ξ := RatModel.ringOn_le_O hξU
  let φ := RatModel.valHom (gPt p ≫ y) ξ (RatModel.range_eq_singleton _ _)
  have ht : S.th x₀ ∈ M.O ξ := hle (hO.le (S.th_mem x₀))
  have ht' : (S.th x₀)⁻¹ ∈ M.O ξ := hle (hO.th_unit x₀ hx₀.1)
  have hg : ∀ k j, (GG₀ k j : Ω) / S.th x₀ ^ a ∈ M.O ξ := fun k j => by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (hle (hO.le (GG₀ k j).2)) (pow_mem ht' a)
  have H := hgen z x₀ hx₀
  have hE := hEE.2 z p y _ τ hz hAt
  rw [hb z hzV] at H hE
  have key := mem_span_map_iff_forall_dotProduct_mem (RatModel.O_le_of_specializes hξ) φ (fun _ => rfl) (OO p)
    (fun x hx => (mem_OO_iff _).2 (RatModel.norm_val_le_one hz.1 hx)) hg b
    ((hb ξ (hξ.mem_open V.isOpen hzV)).symm.trans (hEE.1 ξ hξU)) H
  set u := M.val (gPt p ≫ y) (S.th x₀) with hu
  have hu0 : u ^ a ≠ 0 := pow_ne_zero _ (norm_pos_iff.1 (hδ ▸ τ.δ_pos))
  have e : (fun k j => y' ⟨GG₀ k j, hO.le (GG₀ k j).2⟩ / u ^ a) =
      fun k j => M.val (gPt p ≫ y) ((GG₀ k j : Ω) / S.th x₀ ^ a) := by
    funext k j
    rw [div_eq_iff hu0, hv]
    have h := map_mul φ ⟨_, hg k j⟩ (⟨_, ht⟩ ^ a)
    rw [map_pow] at h
    refine Eq.trans ?_ h
    exact congrArg (M.val (gPt p ≫ y)) (div_mul_cancel₀ _ (pow_ne_zero a hx₀.1)).symm
  rw [mem_span_iff_div_mem_span (OO p) _ hu0, e]
  refine (key _).trans ?_
  rw [← hE]
  refine forall₂_congr fun v _ => ?_
  rw [mem_OO_iff, smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, norm_pow, hδ,
    inv_mul_le_iff₀ (pow_pos τ.δ_pos a), _root_.mul_one]

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomRangeSubset
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem comp_toSpecΓ_eq_valMap {C : Type} [CommRing C] {X : Scheme.{0}} (V : X.Opens) (p : Sp C ⟶ V)
    (h : ⊤ ≤ (p ≫ V.ι) ⁻¹ᵁ V) : p ≫ V.toSpecΓ = Spec.map (valMap (p ≫ V.ι) V h) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, valMap,
    ← Spec.map_comp, ← Spec.map_comp]
  have e : V.topIso.inv ≫ p.appTop = (p ≫ V.ι).appLE V ⊤ h := by
    rw [← Scheme.Hom.appLE_comp_appLE p V.ι V ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  rw [← e]

theorem exists_hom_range_subset {U : M.Z.Opens} (hU : IsAffineOpen U) (hUne : (U : Set M.Z).Nonempty)
    {V : M'.Z.Opens} (hVne : (V : Set M'.Z).Nonempty) (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) :
    ∃ (p : Sp Ω' ⟶ V) (g : (V : Scheme.{0}) ⟶ M.Z), p ≫ V.ι = M'.pt ∧ Set.range g ⊆ U ∧
      p ≫ g = spMap φ.toRingHom ≫ M.pt := by
  let χ : M.ringOn U →+* M'.ringOn V :=
    (φ.toRingHom.comp (M.ringOn U).val.toRingHom).codRestrict (M'.ringOn V) fun x => h x x.2
  let ψ : Γ(M.Z, U) →+* Γ(M'.Z, V) :=
    (M'.sectionsEquiv V hVne).symm.toRingHom.comp (χ.comp (M.sectionsEquiv U hUne).toRingHom)
  have hr : Set.range M'.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M'.top_le_preimage_pt hVne)
  have hp := IsOpenImmersion.lift_fac V.ι M'.pt hr
  set p := IsOpenImmersion.lift V.ι M'.pt hr
  have hp' : p ≫ V.toSpecΓ = Spec.map (valMap M'.pt V (M'.top_le_preimage_pt hVne)) := by
    have := comp_toSpecΓ_eq_valMap V p (hp ▸ M'.top_le_preimage_pt hVne)
    simpa only [hp] using this
  refine ⟨p, V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, hp, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  rw [← Category.assoc, hp']
  conv_rhs => rw [← specMap_valMap_fromSpec hU M.pt (M.top_le_preimage_pt hUne)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  have e : (M'.sectionsEquiv V hVne (ψ a) : Ω') = φ (M.sectionsEquiv U hUne a) :=
    congrArg Subtype.val ((M'.sectionsEquiv V hVne).apply_symm_apply _)
  exact e

theorem IsHom.map_mem_of_ringOn {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set M.Z).Nonempty) {V : M'.Z.Opens} (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) {z : M'.Z}
    (hz : z ∈ V) : f z ∈ U := by
  obtain ⟨p, g, hp, hg, e⟩ := exists_hom_range_subset hU hUne ⟨z, hz⟩ h
  have e' : V.ι ≫ f = g := hom_ext_of_isOpenImmersion V.ι hp (by rw [← Category.assoc, hp]; exact hf) e
  exact hg ⟨⟨z, hz⟩, by rw [← e']; rfl⟩

theorem isAffineOpen_of_isHom (R : Subalgebra o Ω) [Algebra.FiniteType o R] [IsFractionRing R Ω] {U : M.Z.Opens}
    (hR : R ≤ M.ringOn U) {g : (ofAffine o Ω R).Z ⟶ M.Z} (hg : M.IsHom (ofAffine o Ω R) (AlgHom.id o Ω) g)
    (hU : Set.range g ⊆ U) : IsAffineOpen U ∧ M.ringOn U = R := by
  have hne : (U : Set M.Z).Nonempty := ⟨_, hU ⟨genericPoint _, rfl⟩⟩
  refine ⟨?_, le_antisymm (fun x hx => ?_) hR⟩
  · haveI : IsAffine (ofAffine o Ω R).Z := inferInstanceAs (IsAffine (Sp R))
    obtain ⟨p, h, hp, -, e⟩ := exists_hom_range_subset (M := ofAffine o Ω R) (φ := AlgHom.id o Ω)
      (isAffineOpen_top _) ⟨genericPoint _, trivial⟩ hne fun x hx => by
        obtain ⟨a, rfl⟩ := mem_ringOn_univ_ofAffine.1 hx
        exact hR a.2
    have hid : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    have hg' : (ofAffine o Ω R).pt ≫ g = M.pt := by
      have := hg
      rwa [IsHom, hid, Category.id_comp] at this
    have e1 : h ≫ g = U.ι := hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) U.ι hp
      (by rw [← Category.assoc, e, Category.assoc, hg']) (by rw [hp, hid, Category.id_comp])
    have hr : Set.range g ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
    have hl := IsOpenImmersion.lift_fac U.ι g hr
    set l := IsOpenImmersion.lift U.ι g hr
    have e2 : h ≫ l = 𝟙 _ := by rw [← cancel_mono U.ι, Category.assoc, hl, e1, Category.id_comp]
    have e3 : l ≫ h = 𝟙 _ := by
      refine IsHom.unique (φ := AlgHom.id o Ω) ?_ (isHom_id _)
      have : (ofAffine o Ω R).pt ≫ l = p := by rw [← cancel_mono U.ι, Category.assoc, hl, hg', hp]
      rw [IsHom, ← Category.assoc, this, e]
    haveI : IsIso h := ⟨l, e2, e3⟩
    exact IsAffine.of_isIso h
  · obtain ⟨a, rfl⟩ := mem_ringOn_univ_ofAffine.1 (mem_ringOn.2 fun z _ =>
      hg.map_mem_O (mem_ringOn.1 hx (g z) (hU ⟨z, rfl⟩)))
    exact a.2

theorem IsHom.inv_mem_O {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {z : M'.Z} {x : Ω} (hx : x ∈ M.O (f z))
    (h0 : x ≠ 0) (hi : (φ x)⁻¹ ∈ M'.O z) : x⁻¹ ∈ M.O (f z) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have e := hf.valF_app ⟨_, hz⟩ a
  have h1 : z ∈ M'.Z.basicOpen (f.app U a) :=
    (isUnit_valF_iff (U := f ⁻¹ᵁ U) hz _).1 ((isUnit_O_iff _).2 ⟨by simpa [e] using h0, by simpa only [e] using hi⟩)
  rw [← Scheme.preimage_basicOpen] at h1
  exact ((isUnit_O_iff _).1 ((isUnit_valF_iff hz a).2 h1)).2

theorem IsHom.div_of_div {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {J : Type} {t : J → Ω} {i k : J} {z : M'.Z}
    (hk : M.Div t k (f z)) (h : M'.Div (fun j => φ (t j)) i z) : M.Div t i (f z) := by
  have h0 : t i / t k ≠ 0 := div_ne_zero ((map_ne_zero φ).1 h.1) hk.1
  exact (hk.div_iff_isUnit i).2 ((isUnit_O_iff _).2 ⟨h0, hf.inv_mem_O (hk.2 i) h0 (by simpa using h.2 k)⟩)

section Pairing

variable {J : Type} [Fintype J]

def pairing (φ : Ω →ₐ[o] Ω') (s : J → Ω') (v : J → Ω) : Ω' := ∑ j, φ (v j) * s j

theorem pairing_sum {I : Type} [Fintype I] (s : J → Ω') (c : I → Ω) (a : I → J → Ω) :
    pairing φ s (∑ i, c i • a i) = ∑ i, φ (c i) * pairing φ s (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum, _root_.mul_assoc]
  exact Finset.sum_comm

theorem pairing_div (s : J → Ω') (v : J → Ω) (c : Ω) :
    pairing φ s (fun j => v j / c) = (φ c)⁻¹ * pairing φ s v := by
  simp only [pairing, map_div₀, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_pairing_eq {I : Type} [Fintype I] (s : J → Ω') {S : Subalgebra o Ω} {a : I → J → Ω} {v : J → Ω}
    (hv : v ∈ Submodule.span S (Set.range a)) :
    ∃ c : I → Ω, (∀ i, c i ∈ S) ∧ pairing φ s v = ∑ i, φ (c i) * pairing φ s (a i) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  exact ⟨fun i => c i, fun i => (c i).2, pairing_sum s (fun i => (c i : Ω)) a⟩

theorem IsHom.exists_div_pairing {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) (s : J → Ω') {I K : Type} [Fintype I]
    [Fintype K] {a : I → J → Ω} {b : K → J → Ω} {z : M'.Z}
    (h : Submodule.span (M.O (f z)) (Set.range a) = Submodule.span (M.O (f z)) (Set.range b)) {i : I}
    (hi : M'.Div (fun i => pairing φ s (a i)) i z) : ∃ k, M'.Div (fun k => pairing φ s (b k)) k z := by
  have h0 : pairing φ s (a i) ≠ 0 := hi.1
  have h1 : ∀ k, pairing φ s (b k) / pairing φ s (a i) ∈ M'.O z := fun k => by
    obtain ⟨c, hc, e⟩ := exists_pairing_eq (φ := φ) s (h ▸ Submodule.subset_span ⟨k, rfl⟩ :
      b k ∈ Submodule.span (M.O (f z)) (Set.range a))
    rw [e, Finset.sum_div]
    exact sum_mem fun i' _ => by
      rw [mul_div_assoc]
      exact mul_mem (hf.map_mem_O (hc i')) (hi.2 i')
  obtain ⟨d, hd, e⟩ := exists_pairing_eq (φ := φ) s (h ▸ Submodule.subset_span ⟨i, rfl⟩ :
      a i ∈ Submodule.span (M.O (f z)) (Set.range b))
  have e1 : ∑ k, (⟨φ (d k), hf.map_mem_O (hd k)⟩ * ⟨_, h1 k⟩ : M'.O z) = 1 := by
    refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, OneMemClass.coe_one, ← mul_div_assoc,
      ← Finset.sum_div, ← e, div_self h0]
  obtain ⟨k, -, hk⟩ := IsLocalRing.exists_of_isUnit_sum (e1 ▸ isUnit_one)
  obtain ⟨hk0, hk1⟩ := (isUnit_O_iff _).1 (isUnit_of_mul_isUnit_right hk)
  have hk2 : pairing φ s (b k) ≠ 0 := fun h => hk0 (by simp [h])
  refine ⟨k, hk2, fun k' => ?_⟩
  have := mul_mem (h1 k') hk1
  convert this using 1
  field_simp

theorem Lat.exists_eq_sum_pairing [DecidableEq J] (EE : M.Lat J) (s : J → Ω') {I : Type} [Fintype I]
    {a : I → J → Ω} {z : M.Z} (h : EE.E z = Submodule.span (M.O z) (Set.range a)) (j : J) :
    ∃ c : I → Ω, s j = ∑ i, φ (c i) * pairing φ s (a i) := by
  obtain ⟨U, b, hz, hb, H⟩ := EE.loc z
  have h1 : ∀ l, b l ∈ Submodule.span (M.O z) (Set.range a) := fun l =>
    h ▸ H z hz ▸ Submodule.subset_span ⟨l, rfl⟩
  choose c _ hc using fun l => exists_pairing_eq (φ := φ) s (h1 l)
  have e : (Pi.single j 1 : J → Ω) = ∑ l, b⁻¹ j l • b l := by
    ext j'
    have := congrFun (congrFun (Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.2 hb)) j) j'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp [Finset.sum_apply, this, Pi.single_apply, eq_comm]
  have e2 : pairing φ s (Pi.single j 1) = s j := by
    simp [pairing, Pi.single_apply, apply_ite φ]
  refine ⟨fun i => ∑ l, b⁻¹ j l * c l i, ?_⟩
  rw [← e2, e]
  refine (pairing_sum s (fun l => b⁻¹ j l) fun l => b l).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hc, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
  exact Finset.sum_comm

theorem Lat.eq_top_of_pairing_mem [DecidableEq J] (EE : M.Lat J) {s : J → Ω'}
    (hs : Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤) {I : Type} [Fintype I]
    {a : I → J → Ω} {z : M.Z} (h : EE.E z = Submodule.span (M.O z) (Set.range a)) {g : Ω'} (hg : g ≠ 0)
    {K : Subfield Ω'} (h1 : ∀ x, φ x ∈ K) (h2 : ∀ i, pairing φ s (a i) / g ∈ K) : K = ⊤ := by
  have h3 : ∀ j, s j / g ∈ K := fun j => by
    obtain ⟨c, e⟩ := EE.exists_eq_sum_pairing (φ := φ) s h j
    rw [e, Finset.sum_div]
    exact sum_mem fun i _ => by
      rw [mul_div_assoc]
      exact mul_mem (h1 _) (h2 i)
  refine top_unique (hs ▸ Subfield.closure_le.2 ?_)
  rintro _ (⟨x, rfl⟩ | ⟨i, j, rfl⟩)
  · exact h1 x
  · have := div_mem (h3 j) (h3 i)
    rwa [div_div_div_cancel_right₀ hg] at this

end Pairing

theorem map_mem_of_ringOn {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) {K : Subfield Ω'}
    (h : ∀ x ∈ M.ringOn V, φ x ∈ K) (x : Ω) : φ x ∈ K := by
  obtain ⟨a, b, -, rfl⟩ := exists_eq_div hV hne x
  rw [map_div₀]
  exact div_mem (h _ ((mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩)) (h _ ((mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem div_comp_iff {I K : Type} {t : K → Ω} {e : I → K} (he : Function.Surjective e) {i : I} {z : M.Z} :
    M.Div (fun i => t (e i)) i z ↔ M.Div t (e i) z :=
  and_congr_right fun _ => (he.forall (p := fun k => t k / t (e i) ∈ M.O z)).symm

theorem div_mul_prod_iff {I K : Type} {t : I → Ω} {u : K → Ω} {i : I} {k : K} {z : M.Z} :
    M.Div (fun q : I × K => t q.1 * u q.2) (i, k) z ↔ M.Div t i z ∧ M.Div u k z := by
  constructor
  · rintro ⟨h0, h⟩
    have hi : t i ≠ 0 := left_ne_zero_of_mul h0
    have hk : u k ≠ 0 := right_ne_zero_of_mul h0
    exact ⟨⟨hi, fun i' => by simpa [mul_div_mul_right _ _ hk] using h (i', k)⟩,
      ⟨hk, fun k' => by simpa [mul_div_mul_left _ _ hi] using h (i, k')⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_ne_zero h1.1 h2.1, fun q => by simpa [mul_div_mul_comm] using mul_mem (h1.2 q.1) (h2.2 q.2)⟩

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FFDivFFMemOOfValuationRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.FF_div_FF_mem_O_of_valuationRing :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → ∀ x₀ ∈ S.supI M z, ∀ j : ℕ, 1 ≤ j → ∃ C : ℕ, (S.FF _ c' k' / S.th x₀) ^ (j + 1) * (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ^ C / (S.FF _ c k / S.th x₀) ^ j ∈ M.O z) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → IsDomain (M.O ξ) → ValuationRing (M.O ξ) → IsNoetherianRing (M.O ξ) → S.FF _ c' k' / S.FF _ c k ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ hO _ H z ξ c c' k k' hz hs hc hk hk' _ hv hn
  obtain ⟨x₀, hx₀⟩ := hO.div z
  have hx₀' : M.Div S.th x₀ ξ := hx₀.of_specializes hs
  have h0 : S.th x₀ ≠ 0 := hx₀.1
  have hP : (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ≠ 0 ∧ (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀)⁻¹ ∈ M.O ξ := by
    refine finprod_mem_induction (fun u : Ω => u ≠ 0 ∧ u⁻¹ ∈ M.O ξ) ⟨one_ne_zero, by simp⟩ ?_ ?_
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨mul_ne_zero ha hb, by rw [mul_inv]; exact mul_mem ha' hb'⟩
    · intro x hx
      have hx' : M.Div S.th x ξ := hx
      exact ⟨div_ne_zero hx'.1 h0, by rw [inv_div]; exact hx'.2 x₀⟩
  have hval : ∀ x : Ω, x ∈ (M.O ξ).toSubring ∨ x⁻¹ ∈ (M.O ξ).toSubring := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger (M.O ξ) x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inl (hy ▸ y.2)
    · exact Or.inr (hy ▸ y.2)
  haveI : ValuationRing (M.O ξ).toSubring := hv
  haveI : IsNoetherianRing (M.O ξ).toSubring := hn
  have key := div_mem_of_forall_pow_succ_div_pow_mem Ω (M.O ξ).toSubring hval
    (S.FF _ c k / S.th x₀) (S.FF _ c' k' / S.th x₀) (div_ne_zero hk.1 h0) (div_ne_zero hk'.1 h0) (by
      intro j hj
      obtain ⟨C, hC⟩ := H z ξ c c' k k' hz hs hc hk hk' x₀ hx₀ j hj
      have h1 := mul_mem (RatModel.O_le_of_specializes hs hC) (pow_mem hP.2 C)
      have hP1 := hP.1
      generalize (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) = P at h1 hP1
      rw [div_mul_eq_mul_div, _root_.mul_assoc, ← _root_.mul_pow, mul_inv_cancel₀ hP1, _root_.one_pow, _root_.mul_one] at h1
      exact h1)
  rw [div_div_div_cancel_right₀ h0] at key
  exact key

end GlobalTheory.ZH
end

