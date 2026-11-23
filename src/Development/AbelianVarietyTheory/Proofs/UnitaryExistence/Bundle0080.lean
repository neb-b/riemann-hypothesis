module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
section
noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem markMove_finVec_mem {D : D7} (V : HSp D) (g : GA D V) {v : Fin V.rank → D.host.E} (hv : v ∈ latG V g) :
    finVec V v ∈ latGHat V g := by
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.2.1]
  exact AddSubgroup.subset_closure ⟨1, fun w => one_mem _, v, hv, rfl⟩

theorem markMove_mulVec_mem {D : D7} (V : HSp D) (g : GA D V)
    {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ latGHat V 1) :
    (finHom V g).1 *ᵥ y ∈ latGHat V g := by
  have h := (GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.1
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1] at hy
  rw [← SetLike.mem_coe, h]
  exact ⟨y, hy, rfl⟩

theorem markMove_finVec_add_nsmul {D : D7} (V : HSp D) (x y : Fin V.rank → D.host.E) (n : ℕ) :
    finVec V (x + n • y) = finVec V x + n • finVec V y := by
  funext i
  simp only [finVec, Pi.add_apply, Pi.smul_apply, TensorProduct.tmul_add]
  congr 1
  exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) n (y i)

theorem markMove_mulVec_nsmul {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (n : ℕ)
    (y : Fin m → R) : A *ᵥ (n • y) = n • (A *ᵥ y) := Matrix.mulVec_smul _ _ _

theorem markMove_finHom_mul {D : D7} (V : HSp D) (g h : GA D V)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (g * h)).1 *ᵥ y = (finHom V g).1 *ᵥ ((finHom V h).1 *ᵥ y) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]


set_option maxHeartbeats 800000 in
theorem mark_move : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k γ, C.Mark h k γ → (∀ γ₀ ∈ GQ V, C.Mark (γ₀ * h) k (γ * γ₀⁻¹)) ∧ (∀ u, FinCong V l.M u → C.Mark (h * u) k γ) ∧ (∀ u ∈ GinfC V, C.Mark (h * u) k γ) ∧ ∀ δ ∈ (C.M.X k).Γ, ∃ γ₁ ∈ GQ V, C.Mark h k (γ₁ * γ) ∧ C.fr (γ₁ * γ * h) k = lact δ (C.fr (γ * h) k) := by
  intro D H Dw l Xo c σ V r C hC h k γ hM
  obtain ⟨hγ, hΛ, hmk⟩ := hM
  refine ⟨fun γ₀ hγ₀ => ?_, fun u hu => ?_, fun u hu => ?_, fun δ hδ => ?_⟩
  · have e : γ * γ₀⁻¹ * (γ₀ * h) = γ * h := by group
    refine ⟨mul_mem hγ (inv_mem hγ₀), ?_, ?_⟩
    · rw [e]; exact hΛ
    · rw [e]; exact hmk
  · have e : γ * (h * u) = γ * h * u := (mul_assoc _ _ _).symm
    obtain ⟨e1, e2⟩ := (GlobalTheory.Member.latG_move D V).2.2.1 l.M (γ * h) u hu
    refine ⟨hγ, ?_, ?_⟩
    · rw [e, e1]; exact hΛ
    · intro a ha
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      have hιa : C.ι a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • latG V 1 := by
        rw [← hC.iota.emb.2, ← Submodule.map_top, ← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem ha
      obtain ⟨y, hy, hy'⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V u).2 l.M _).1 (((GlobalTheory.Member.finCong_iff_half_and_kfHalf D H l V).1 u).1 hu) _ hιa
      rw [e, e2]
      refine ⟨w - (finHom V (γ * h)).1 *ᵥ y, sub_mem hw (markMove_mulVec_mem V _ hy), ?_⟩
      rw [markMove_finHom_mul, sub_eq_iff_eq_add'.1 hy', Matrix.mulVec_add, markMove_mulVec_nsmul, nsmul_sub, ← hw',
        sub_add_eq_sub_sub]
  · have e : finHom V (γ * (h * u)) = finHom V (γ * h) := by
      have hu' : finHom V u = 1 := hu
      rw [← mul_assoc, map_mul _ _ u, hu', mul_one]
    obtain ⟨e1, e2⟩ := (GlobalTheory.Member.latG_move D V).2.1 _ _ e
    refine ⟨hγ, ?_, ?_⟩
    · rw [e1]; exact hΛ
    · rw [e2, e]; exact hmk
  · have hr := C.hr
    subst hr
    obtain ⟨⟨hU, hS⟩, hcong, -⟩ := (hC.base.gam k δ).1 hδ
    have hG : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
    rw [hG] at hU
    obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.Member.RatElt.rational_elements D V
    obtain ⟨γ₁, hγ₁⟩ := r3 δ hU
    have hq : γ₁ ∈ GQ V := (r1 γ₁).2 ⟨δ, hγ₁⟩
    obtain ⟨m1, m2⟩ := (GlobalTheory.Member.latG_move D V).1 γ₁ δ (γ * h) hγ₁
    obtain ⟨f1, f2⟩ := r5 γ₁ δ hγ₁
    have hΛ' : ∀ v, v ∈ (C.M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
      rw [← SetLike.mem_coe, hΛ]
      exact ⟨fun ⟨x, hx, e⟩ => (show x = v from e) ▸ hx, fun hv => ⟨v, hv, rfl⟩⟩
    have hΛ'' : ∀ v, v ∈ (C.M.X k).Λ ↔ v ∈ latG V (γ₁ * (γ * h)) := fun v => by
      have e : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
          (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have h0 := ((hS _).symm.trans (hΛ' (((δ⁻¹ : GL (Fin V.rank) D.host.E) :
        Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v))).trans (m1 _)
      rwa [e] at h0
    refine ⟨γ₁, hq, ⟨mul_mem hq hγ, ?_, ?_⟩, ?_⟩
    · rw [mul_assoc]
      ext v
      rw [SetLike.mem_coe, hΛ'']
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨x, hx, e⟩ => (show x = v from e) ▸ hx⟩
    · intro a ha
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      have hta : C.F.t k a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) •
          (⊤ : Submodule (𝓞 D.host.E) (C.F.Di k).La) := by
        have h1 := Submodule.mem_map_of_mem (f := C.F.t k) ha
        rw [Submodule.map_smul''] at h1
        exact Submodule.smul_mono le_rfl le_top h1
      obtain ⟨b, hb⟩ := hcong _ hta
      rw [mul_assoc]
      refine ⟨(finHom V γ₁).1 *ᵥ w - finVec V (C.M.φ k b : Fin V.rank → D.host.E),
        sub_mem ((m2 w).1 hw) (markMove_finVec_mem V _ ((hΛ'' _).1 (C.M.φ k b).2)), ?_⟩
      have hw2 : finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) -
          (finHom V (γ * h)).1 *ᵥ (finVec V (C.ι a)) = (l.M : ℕ) • w := hw'
      have h3 := f1 (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E)
      rw [hb, markMove_finVec_add_nsmul] at h3
      show finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      rw [markMove_finHom_mul, nsmul_sub, ← markMove_mulVec_nsmul, ← hw2, Matrix.mulVec_sub, h3]
      abel
    · funext τ
      have a1 := ((GlobalTheory.Member.Arch.archM_spec D V C.θ hC.inf).1 τ.1).2.1 γ₁ (γ * h)
      have a2 := f2 τ.1 (C.θ τ.1) (hC.inf τ.1)
      show (archM V (C.θ τ.1) (γ₁ * γ * h) * C.x₀ τ.1 : Matrix _ _ ℂ) =
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * (archM V (C.θ τ.1) (γ * h) * C.x₀ τ.1)
      rw [mul_assoc γ₁, a1, a2, Matrix.mul_assoc]

end GlobalTheory.Member
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.CubeGlue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem triv_of_triv_pull_id {P : Scheme.{0}} {M : LB P} (h : Triv (M.pull (𝟙 P))) : Triv M := by
  obtain ⟨u, hu⟩ := h
  have le : ∀ i, M.U i ≤ (M.pull (𝟙 P)).U (fun _ => i) := fun i y hy => mem_pull.2 hy
  refine ⟨⟨fun i => res (le i) (u.s fun _ => i)⟩, fun i j => unit_ext fun y hy => ?_⟩
  have c := gen_trans hu (𝟙 P) y (le i hy.1) (le j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp] at c
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (c.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))

theorem exists_section {P Z : Scheme.{0}} (p : P ⟶ Z) (e : Z ⟶ P) (he : e ≫ p = 𝟙 Z) (V : Z.Opens) :
    ∃ s : V.toScheme ⟶ (p ⁻¹ᵁ V).toScheme, s ≫ (p ⁻¹ᵁ V).ι = V.ι ≫ e ∧ s ≫ (p ∣_ V) = 𝟙 _ := by
  obtain ⟨s, hs⟩ : ∃ s : V.toScheme ⟶ (p ⁻¹ᵁ V).toScheme, s ≫ (p ⁻¹ᵁ V).ι = V.ι ≫ e :=
    ⟨IsOpenImmersion.lift _ (V.ι ≫ e) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (· ∈ V) (congrArg (fun m => m q.1) he)).mpr q.2), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨s, hs, ?_⟩
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hs, Category.assoc, he,
    Category.id_comp, Category.comp_id]

theorem exists_normalised {P Z : Scheme.{0}} {M : LB P} (hM : M.IsLB) (p : P ⟶ Z) (e : Z ⟶ P) (he : e ≫ p = 𝟙 Z)
    (g : LB.Gen (M.pull e)) (hg : g.IsGen) (V : Z.Opens) (h : Triv (M.pull (p ⁻¹ᵁ V).ι)) :
    ∃ t : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => (p ⁻¹ᵁ V).ι ≫ 𝟙 P) (fun _ => 1)), t.IsGen ∧
      ∀ (T : Scheme.{0}) (r : T ⟶ (p ⁻¹ᵁ V).toScheme) (b : T ⟶ Z) (z : T) (J), Good M z J →
        r ≫ (p ⁻¹ᵁ V).ι = b ≫ e → val t r z J = val g b z J := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs, -⟩ := exists_section p e he V
  have n₁ : ((p ∣_ V) ≫ s) ≫ (p ⁻¹ᵁ V).ι = ((p ⁻¹ᵁ V).ι ≫ p) ≫ e := by
    rw [Category.assoc, hs, ← Category.assoc, morphismRestrict_ι]
  obtain ⟨t', ht', hv⟩ := exists_gen hM (K' := PUnit) (φ' := fun _ => (p ⁻¹ᵁ V).ι ≫ 𝟙 P) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁, Category.comp_id]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ t (LB.invGen M _ _ (LB.pullGen M _ _ t ((p ∣_ V) ≫ s))))
      (LB.pullGen M _ _ g ((p ⁻¹ᵁ V).ι ≫ p)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hg _))
  refine ⟨t', ht', fun T r b z J hJ hr => ?_⟩
  have hb : r ≫ (p ⁻¹ᵁ V).ι ≫ p = b := by
    rw [← Category.assoc, hr, Category.assoc, he, Category.comp_id]
  have : r ≫ (p ∣_ V) ≫ s = r := by
    rw [← cancel_mono (p ⁻¹ᵁ V).ι, Category.assoc, n₁, ← Category.assoc, hb, hr]
  rw [hv T r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, this, mul_inv_cancel, hb,
    _root_.one_mul]

theorem triv_of_locally_triv {P Z : Scheme.{0}} {M : LB P} (hM : M.IsLB) (p : P ⟶ Z) (e : Z ⟶ P)
    (he : e ≫ p = 𝟙 Z) (hp : ∀ V : Z.Opens, Function.Surjective (p ∣_ V).appTop.hom) (h₀ : Triv (M.pull e))
    (loc : ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧ Triv (M.pull (p ⁻¹ᵁ V).ι)) : Triv M := by
  obtain ⟨g, hg⟩ := h₀
  choose U hU hT using loc
  choose t ht hn using fun z => exists_normalised hM p e he g hg (U z) (hT z)
  obtain ⟨u, hu, -⟩ := glue_gen hM (K := PUnit) (fun _ => 𝟙 P) (fun _ => 1) (fun s => p ⁻¹ᵁ U s)
    (fun y => ⟨p y, hU _⟩) t ht (by
      intro s s' T r r' z J hJ hr
      obtain ⟨σ, hσ, hσ'⟩ := exists_section p e he (U s ⊓ U s')
      let m := P.homOfLE (show p ⁻¹ᵁ (U s ⊓ U s') ≤ p ⁻¹ᵁ U s from fun _ hy => hy.1)
      let m' := P.homOfLE (show p ⁻¹ᵁ (U s ⊓ U s') ≤ p ⁻¹ᵁ U s' from fun _ hy => hy.2)
      have hm : m ≫ (p ⁻¹ᵁ U s).ι = (p ⁻¹ᵁ (U s ⊓ U s')).ι := P.homOfLE_ι _
      have hm' : m' ≫ (p ⁻¹ᵁ U s').ι = (p ⁻¹ᵁ (U s ⊓ U s')).ι := P.homOfLE_ι _
      obtain ⟨ρ, hρ⟩ : ∃ ρ : T ⟶ (p ⁻¹ᵁ (U s ⊓ U s')).toScheme, ρ ≫ (p ⁻¹ᵁ (U s ⊓ U s')).ι = r ≫ (p ⁻¹ᵁ U s).ι :=
        ⟨IsOpenImmersion.lift _ (r ≫ (p ⁻¹ᵁ U s).ι) (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
      have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
      have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
      have key := gen_unique' hM (K := PUnit) (K' := PUnit) (φ := fun _ => m ≫ (p ⁻¹ᵁ U s).ι ≫ 𝟙 P) (ε := fun _ => 1)
        (φ' := fun _ => m' ≫ (p ⁻¹ᵁ U s').ι ≫ 𝟙 P) (ε' := fun _ => 1)
        (fun W _ k => Finset.prod_congr rfl fun i _ => by
          show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
          rw [← Category.assoc, ← Category.assoc m, hm, hm'])
        (p ∣_ (U s ⊓ U s')) σ hσ' (hp _) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
        (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
          rw [val_pull hI, val_pull hI, hn s _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm, hσ]),
            hn s' _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm', hσ])]) T ρ z J hJ
      rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key)
  exact triv_of_triv_pull_id ⟨u, hu⟩

theorem surjective_restrict {P Z : Scheme.{0}} (p : P ⟶ Z) (h : ∀ V : Z.Opens, IsIso (p.app V)) (V : Z.Opens) :
    Function.Surjective (p ∣_ V).appTop.hom := by
  have : IsIso (p ∣_ V).appTop := by
    rw [morphismRestrict_appTop]
    have := h (V.ι ''ᵁ ⊤)
    refine IsIso.comp_isIso' this ?_
    rw [eqToHom_op]; exact Functor.map_isIso _ _
  exact (ConcreteCategory.bijective_of_isIso (p ∣_ V).appTop).2

theorem triv_of_triv_faces : ∀ (k : Type) [Field k] (X Y Z : Over (Sp k)) (x₀ : 𝟙_ (Over (Sp k)) ⟶ X) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (z₀ : 𝟙_ (Over (Sp k)) ⟶ Z), Smooth X.hom → Smooth Y.hom → IsProper X.hom → IsProper Y.hom → IsProjBy X.hom → IsProjBy Y.hom → GeometricallyIntegral X.hom → GeometricallyIntegral Y.hom → ConnectedSpace Z.left → ∀ M : LB (X ⊗ Y ⊗ Z).left, M.IsLB → Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) → Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left) → Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left) → Triv M := by
  intro k _ X Y Z x₀ y₀ z₀ sX sY pX pY jX jY gX gY cZ M hM h₁ h₂ h₃
  have loc := GlobalTheory.T.theorem_of_cube_locally_two_projective_factors k X Y Z x₀ y₀ z₀ sX sY pX pY jX jY gX gY cZ M hM h₁ h₂ h₃
  have iX : ∀ V, IsIso ((snd X (Y ⊗ Z)).left.app V) := fun V =>
    GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field (IsPullback.of_hasPullback X.hom (Y ⊗ Z).hom) V
  have iY : ∀ V, IsIso ((snd Y Z).left.app V) := fun V =>
    GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field (IsPullback.of_hasPullback Y.hom Z.hom) V
  let σ : Z ⟶ Y ⊗ Z := lift (toUnit Z ≫ y₀) (𝟙 Z)
  obtain ⟨g, hg⟩ := h₁
  refine triv_of_locally_triv hM (snd X (Y ⊗ Z) ≫ snd Y Z).left
    (σ.left ≫ (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) ?_ (surjective_restrict _ fun V => ?_)
    ⟨_, DVR.pullGen_isGen _ _ _ _ hg σ.left⟩ loc
  · rw [← Over.comp_left, ← Over.comp_left]
    exact congrArg (fun q => q.left)
      (show (σ ≫ lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))) ≫ snd X (Y ⊗ Z) ≫ snd Y Z = 𝟙 Z by simp [σ])
  · rw [Over.comp_left, Scheme.Hom.comp_app]
    exact IsIso.comp_isIso' (iY V) (iX _)

end GlobalTheory.CubeGlue
end

