module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import GroundTheory.PAdicHodge.TiltField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfMemCcAt
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

noncomputable section

namespace GlobalTheory.CutFam

theorem exists_of_mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X)
    {c : O} (hc : c ∈ ccAt T Z π) : ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = c := by
  unfold ccAt Ideal.map at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact ⟨f, hf, rfl⟩
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f + g, add_mem hf hg, rfl⟩
  | smul r x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine ⟨algebraMap O T r * f, Ideal.mul_mem_left _ _ hf, ?_⟩
    simp [smul_eq_mul]

theorem mem_ccIdeal_iff {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (f : T) :
    f ∈ ccIdeal T Z ↔ ∀ y, y ∉ Z → (f : X → O) y = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h y hy
    have := congrFun h ⟨y, hy⟩
    simpa using this
  · intro h
    funext y
    simpa using h y.1 y.2

theorem exists_ne_zero {O X : Type} [CommRing O] [IsDomain O] [Fintype X] (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (Z : Finset X) (π : X) (hπ : π ∈ Z) :
    ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π ≠ 0 := by
  classical
  have h : ∀ x : {x // x ∉ Z}, ∃ f : T, (f : X → O) x.1 ≠ (f : X → O) π := by
    intro x
    obtain ⟨f, hfT, hf⟩ := hsep x.1 π (fun h => x.2 (h ▸ hπ))
    exact ⟨⟨f, hfT⟩, hf⟩
  choose g hg using h
  refine ⟨∏ x : {x // x ∉ Z}, (g x - algebraMap O T ((g x : X → O) x.1)), ?_, ?_⟩
  · rw [mem_ccIdeal_iff]
    intro y hy
    change (T.val.toMonoidHom (∏ x : {x // x ∉ Z}, (g x - algebraMap O T ((g x : X → O) x.1)))) _ = _
    rw [map_prod, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨y, hy⟩) ?_
    simp
  · change (T.val.toMonoidHom (∏ x : {x // x ∉ Z}, (g x - algebraMap O T ((g x : X → O) x.1)))) _ ≠ _
    rw [map_prod, Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun x _ => ?_
    have e : ∀ c : O, ((algebraMap O T c : T) : X → O) π = c := fun c => by simp
    change ((g x - algebraMap O T ((g x : X → O) x.1) : T) : X → O) π ≠ 0
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, e]
    exact sub_ne_zero.mpr (hg x).symm

theorem length_span {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : t ≠ 0) :
    Module.length O (O ⧸ Ideal.span {t}) = IsDiscreteValuationRing.addVal O t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n]
  have : Ideal.span {(u : O) * ϖ ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

theorem lenUnit_mul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) {a b : O}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    lenUnit (O := O) l (O ⧸ Ideal.span {a * b}) =
      lenUnit (O := O) l (O ⧸ Ideal.span {a}) + lenUnit (O := O) l (O ⧸ Ideal.span {b}) := by
  unfold lenUnit
  rw [length_span _ (mul_ne_zero ha hb), length_span _ ha, length_span _ hb,
    IsDiscreteValuationRing.addVal_mul]
  have h1 : IsDiscreteValuationRing.addVal O a ≠ ⊤ := fun h =>
    ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  have h2 : IsDiscreteValuationRing.addVal O b ≠ ⊤ := fun h =>
    hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  rw [ENat.toNat_add h1 h2]
  push_cast
  rw [add_div]

variable {D : D7}

theorem act_bc_eig (i : D.nd.Loc) (f : D.nd.T i) (x : D.nd.X i)
    {u : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)}
    (hu : u ∈ heckeEig (D.nd.T i) (D.nd.act i) x) :
    (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u = ((f : D.nd.X i → D.nd.O i) x) • u := by
  have h := (Submodule.mem_iInf _).mp hu f
  rw [Module.End.mem_eigenspace_iff] at h
  rw [h, algebraMap_smul]

theorem bc_mem_eig (i : D.nd.Loc) (β : Module.End (D.nd.O i) (D.nd.Mt i))
    (hβ : ∀ f : D.nd.T i, β * D.nd.act i f = D.nd.act i f * β) (x : D.nd.X i)
    {u : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)}
    (hu : u ∈ heckeEig (D.nd.T i) (D.nd.act i) x) :
    β.baseChange (FractionRing (D.nd.O i)) u ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  refine (Submodule.mem_iInf _).mpr fun f => ?_
  have h := (Submodule.mem_iInf _).mp hu f
  rw [Module.End.mem_eigenspace_iff] at h ⊢
  have e : (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) (β.baseChange (FractionRing (D.nd.O i)) u) =
      β.baseChange (FractionRing (D.nd.O i)) ((D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u) := by
    rw [← Module.End.mul_apply, ← LinearMap.baseChange_mul, ← hβ f, LinearMap.baseChange_mul,
      Module.End.mul_apply]
  rw [e, h, map_smul]

theorem perPoint (i : D.nd.Loc) (k : Fin 2) (π : D.nd.X i) (Xs : Set (D.nd.X i))
    (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i) (h : CutAt i k π Xs β b) :
    ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.O i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
      a ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, α.baseChange (FractionRing (D.nd.O i)) u = a • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) ≤
        vccCut i Xs π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard := by
  classical
  obtain ⟨_, hπZ, hXZ, hcomm, hb0, hbπ, hbout, hblen⟩ := h
  have hπc : π ∈ cutLocus i Xs := by simp [cutLocus, hπZ]
  obtain ⟨f0, hf0, hf0π⟩ := exists_ne_zero (D.nd.T i) (D.nd.T_sep i) _ π hπc
  obtain ⟨c, hc⟩ : ∃ c, ccAt (D.nd.T i) (cutLocus i Xs) π = Ideal.span {c} :=
    ⟨Submodule.IsPrincipal.generator _, (Ideal.span_singleton_generator _).symm⟩
  have hcI : c ∈ ccAt (D.nd.T i) (cutLocus i Xs) π := hc ▸ Ideal.mem_span_singleton_self c
  obtain ⟨g, hg, hgπ⟩ := exists_of_mem_ccAt _ _ _ hcI
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hm : ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) π).comp (D.nd.T i).val.toRingHom) f0 ∈
        ccAt (D.nd.T i) (cutLocus i Xs) π := Ideal.mem_map_of_mem _ hf0
    rw [hc, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hm
    exact hf0π hm
  refine ⟨D.nd.act i g * β, c * b, ?_, ?_, mul_ne_zero hc0 hb0, ?_, ?_⟩
  · intro f
    rw [mul_assoc, hcomm f, ← mul_assoc, ← map_mul, mul_comm g f, map_mul, mul_assoc]
  · intro x hx u hu
    rw [LinearMap.baseChange_mul, Module.End.mul_apply]
    by_cases hxs : x ∈ Xs
    · have hxZ : x ∉ D.nd.Z i := fun hz => hx (hXZ x hxs hz)
      have hxc : x ∉ cutLocus i Xs := by simp [cutLocus, hxZ, hxs]
      rw [act_bc_eig i g x (bc_mem_eig i β hcomm x hu), (mem_ccIdeal_iff _ _ g).mp hg x hxc, zero_smul]
    · rw [hbout x hxs u hu, map_zero]
  · intro u hu
    rw [LinearMap.baseChange_mul, Module.End.mul_apply, hbπ u hu, LinearMap.map_smul_of_tower,
      act_bc_eig i g π hu, hgπ, smul_smul, mul_comm]
  · unfold vccCut
    rw [lenUnit_mul _ hc0 hb0, ← hc]
    linarith

theorem fam_of_cut : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ),
    CongruenceLocalDecomposition CT i k ρ eta → CongruenceFamilyEndomorphisms CT i k ρ eta := by
  intro D CT i k ρ eta hcut
  classical
  obtain ⟨Xs, β, b, h⟩ := hcut
  have hp : ∀ π ∈ D.nd.Zgood i, ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.O i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
      a ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, α.baseChange (FractionRing (D.nd.O i)) u = a • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) ≤
        vccCut i (Xs π) π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard :=
    fun π hπ => perPoint i k π (Xs π) (β π) (b π) (h π hπ).1
  choose! α a hα using hp
  refine ⟨α '' ((D.nd.Zgood i : Finset (D.nd.X i)) : Set (D.nd.X i)), a, fun π => vccCut i (Xs π) π, ?_, ?_⟩
  · rintro _ ⟨π, hπ, rfl⟩
    exact ⟨(hα π hπ).1, (hα π hπ).2.1⟩
  · intro π hπ
    obtain ⟨_, _, h3, h4, h5⟩ := hα π hπ
    exact ⟨h3, ⟨α π, ⟨π, hπ, rfl⟩, h4⟩, h5, (h π hπ).2⟩

end GlobalTheory.CutFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalFamilyResidueZeros
section
noncomputable section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.CoreOrth

theorem core (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [IsAlgClosed F] [CharP F l] [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l])
    (hn : ∀ z, ‖tsh z‖ = ‖z‖) (hs : ∀ x, tsh (ι x) = sh x) (hon : ∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z)
    (h : ℕ) (μ : Fin h → ℂ_[l]) (h2 : 2 ≤ h) (hμ : ∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1)
    (hanti : Antitone (fun i => ‖μ i‖)) (hratio : ∀ i j, ‖μ i‖ < l * ‖μ j‖)
    (horth : ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) :
    ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧
      (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧
      ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  obtain ⟨-, -, -, -, -, hsurj, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hnι : ∀ x, ‖ι x‖ = ‖sh x‖ := fun x => by rw [← hn, hs]
  choose m hm using fun j => hsurj (μ j) (hμ j).2
  obtain ⟨w, hw⟩ := hsurj (l : ℂ_[l]) (by rw [GlobalTheory.PSer.Laws.norm_l]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  set ϖ : F := ι w with hϖdef
  have hϖ : ‖ϖ‖ = (l : ℝ)⁻¹ := by rw [hnι, hw, GlobalTheory.PSer.Laws.norm_l]
  have hϖs : tsh ϖ = l := by rw [hs, hw]
  set lamF : Fin h → F := fun j => ι (m j) with hlamF
  have hnl : ∀ j, ‖lamF j‖ = ‖μ j‖ := fun j => by simp only [lamF, hnι, hm]
  have hmu : ∀ j, sh (m j) = μ j := hm
  have horthF : GlobalTheory.PMonE.Orth l lamF := by
    intro c j hc
    have := _root_.GlobalTheory.tilt_orth_of_untilt_orth l h m (fun i j => by rw [hmu, hmu]; exact hratio i j) (fun c j => by simp only [hmu]; exact horth c j) c j hc
    have e : (∑ i, (c i : F) * lamF i) = ι (∑ i, (c i : Fl l) * m i) := by simp [lamF, map_sum]
    rw [e, hnι, hnι]; exact this
  have hpos : 0 < h := by omega
  obtain ⟨ρ, τ, K, hρ, hτ, hW1, hW2, hW3⟩ := _root_.GlobalTheory.PMonE.winThm F l h ϖ hpos hϖ lamF
    (fun j => by rw [← norm_pos_iff, hnl]; exact norm_pos_iff.2 (hμ j).1)
    (fun i j hij => by simp only [hnl]; exact hanti hij) horthF (fun i j => by simp only [hnl]; exact hratio i j)
  set S : Set (Fin h → Fl l) := {x | ∀ j, ‖sh (x j)‖ ≤ ρ j} with hSdef
  let η : (Fin h → Fl l) → Fin h → ℂ_[l] := fun x i => ∑ j, sh (m j) * lam h i (x j)
  have hE : ∀ x ∈ S, ∀ i, ‖η x i - tsh (GlobalTheory.PMonE.rowT l ϖ lamF K (fun j => ι (x j)) i)‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro x hx i
    exact _root_.GlobalTheory.PSer.row_lam_sub_untilt_rowT l F ι tsh hn hs hon h m x ϖ K τ i (by omega) hϖs (fun j => (hx j).trans_lt (hρ j).2)
      (fun j n => hW1 (fun j => ι (x j)) (fun j => by rw [hnι]; exact hx j) i j n)
  have hpre : ∀ z : Fin h → F, (∀ j, ‖z j‖ ≤ ρ j) → ∃ x ∈ S, (fun j => ι (x j)) = z := by
    intro z hz
    choose x hx using fun j => hon (z j) ((hz j).trans (hρ j).2.le)
    refine ⟨x, fun j => ?_, funext hx⟩
    rw [← hnι, hx]; exact hz j
  have hL1 : ∀ t : Fin h → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro t ht
    choose b hb using fun i => _root_.GlobalTheory.PSer.TshOnto.tsh_surjective l F ι tsh hn hs hon (t i)
    obtain ⟨z, hz, hrow⟩ := hW2 b (fun i => by rw [← hn, hb]; exact ht i)
    obtain ⟨x, hxS, hxz⟩ := hpre z hz
    refine ⟨x, hxS, fun i => ?_⟩
    have := hE x hxS i
    rwa [hxz, hrow, hb] at this
  obtain ⟨z0, hz0, ⟨j0, hj0⟩, hrow0⟩ := hW3
  obtain ⟨x0, hx0S, hx0z⟩ := hpre z0 hz0
  have hL2 : ∀ i, ‖η x0 i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro i
    have := hE x0 hx0S i
    rwa [hx0z, hrow0, map_zero, sub_zero] at this
  obtain ⟨y, hy0, hyS, hysum⟩ := _root_.GlobalTheory.lift_hasSum_zero l (Fin h → Fl l) (Fin h) η τ S hL1 x0 hx0S hL2
  haveI : Nonempty (Fin h) := ⟨⟨0, hpos⟩⟩
  set R : ℝ := Finset.univ.sup' Finset.univ_nonempty ρ with hRdef
  have hρR : ∀ j, ρ j ≤ R := fun j => Finset.le_sup' ρ (Finset.mem_univ j)
  have hR1 : R < 1 := (Finset.sup'_lt_iff _).2 fun j _ => (hρ j).2
  refine ⟨fun j k => y k j, j0, ρ j0, R, (hρ j0).1.le, (hρ j0).2, hR1,
    fun a k => (hyS k a).trans (hρR a), fun k => hyS k j0, ?_, ?_⟩
  · show ρ j0 ^ l ^ h < ‖sh (y 0 j0)‖
    rw [hy0, ← hnι]
    have := congrFun hx0z j0
    rw [this]; exact hj0
  · intro i
    refine _root_.GlobalTheory.PSer.sum_mul_Lam_eq_zero l h μ i y R (by omega) hR1 (fun k j => (hyS k j).trans (hρR j)) ?_
    have := hysum i
    simpa [η, hmu] using this

end GlobalTheory.CoreOrth

namespace GlobalTheory.CoreOrth

theorem residue_zeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → (∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1) → Antitone (fun i => ‖μ i‖) → (∀ i j, ‖μ i‖ < l * ‖μ j‖) → (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) → ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧ (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧ ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  intro l _ h μ h2 hμ hanti hratio horth
  obtain ⟨hac, ι, hs, hon⟩ := GlobalTheory.PSer.tilt_isAlgClosed_and_unitBall l
  haveI := hac
  exact core l _ ι (GroundTheory.PAdicHodge.tiltSharp ℂ_[l] l) (fun z => GroundTheory.PAdicHodge.norm_tiltSharp z) hs hon
    h μ h2 hμ hanti hratio horth
end GlobalTheory.CoreOrth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntSpanImageLatticeRegular
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem exists_zl_span_lattice_reads : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)), Continuous r → ∃ (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Continuous ρ ∧ Reads ρ r b e ∧ LinearIndependent ℚ_[l] b ∧ ∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • (r h).val := by
  intro l _ Γ _ _ _ _ a r hr
  classical
  have hz : ∀ c : ℤ_[l], zOm l c = algebraMap ℤ_[l] (Om l) c := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l) c).symm
  have hsm : ∀ (c : ℤ_[l]) (x : Matrix (Fin a) (Fin a) (Om l)), c • x = zOm l c • x := by
    intro c x; ext i j; simp [Matrix.smul_apply, Algebra.smul_def, hz]
  have hsq : ∀ (c : ℤ_[l]) (x : Matrix (Fin a) (Fin a) (Om l)), c • x = (c : ℚ_[l]) • x := by
    intro c x; rw [hsm]; ext i j; simp [Matrix.smul_apply, Algebra.smul_def, zOm]
  let v : Γ → Matrix (Fin a) (Fin a) (Om l) := fun h => (r h).val
  let M : Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) := Submodule.span ℤ_[l] (Set.range v)

  obtain ⟨t, ht⟩ := GlobalTheory.zl_span_image_finite l Γ a r hr
  have hfg : M.FG := by
    refine ⟨t.image v, le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image]; exact Submodule.span_mono (Set.image_subset_range _ _)
    · rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      obtain ⟨f', hf't, hf'⟩ := ht (Finsupp.single h 1)
      have hvh : v h = f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
          ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
        rw [← hf', Finsupp.sum_single_index (by simp)]
        simp [v]
      rw [SetLike.mem_coe, hvh]
      refine Submodule.sum_mem _ fun k hk => ?_
      have : ((algebraMap ℚ_[l] (PadicAlgCl l)) (f' k : ℚ_[l])) •
          ((r k : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) = f' k • v k := by
        rw [hsm]; rfl
      refine (show _ ∈ _ from ?_)
      beta_reduce
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem v (hf't hk))))
  haveI : Module.Finite ℤ_[l] M := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree ℤ_[l] M := Module.IsTorsionFree.of_smul_eq_zero fun c m h => by
    have h' : (c : ℚ_[l]) • (m : Matrix (Fin a) (Fin a) (Om l)) = 0 := by
      rw [← hsq]; exact congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h0
  haveI : Module.Free ℤ_[l] M := Module.free_of_finite_type_torsion_free'
  let d := Module.finrank ℤ_[l] M
  let B : Module.Basis (Fin d) ℤ_[l] M := Module.finBasis ℤ_[l] M

  have hstab : ∀ (g : Γ) (x : Matrix (Fin a) (Fin a) (Om l)), x ∈ M → v g * x ∈ M := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      exact Submodule.subset_span ⟨g * h, by simp [v, map_mul]⟩
    | zero => simp
    | add y z _ _ hy hz => rw [Matrix.mul_add]; exact M.add_mem hy hz
    | smul c y _ hy => rw [Matrix.mul_smul]; exact M.smul_mem c hy
  let Lm : Γ → Module.End ℤ_[l] M := fun g =>
    { toFun := fun x => ⟨v g * x, hstab g x x.2⟩
      map_add' := fun x y => Subtype.ext (Matrix.mul_add _ _ _)
      map_smul' := fun c x => Subtype.ext (Matrix.mul_smul _ _ _) }
  let L : Γ →* Module.End ℤ_[l] M :=
    { toFun := Lm
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp [Lm, v])
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by simp [Lm, v, map_mul, Matrix.mul_assoc]) }
  let ρ₀ : Γ →* Matrix (Fin d) (Fin d) ℤ_[l] :=
    (LinearMap.toMatrixAlgEquiv B).toAlgHom.toRingHom.toMonoidHom.comp L
  let ρ : Γ →* GL (Fin d) ℤ_[l] := ρ₀.toHomUnits
  have hρ : ∀ g i j, (ρ g).val i j = B.repr (Lm g (B j)) i := by
    intro g i j
    exact LinearMap.toMatrixAlgEquiv_apply B (L g) i j
  let b : Fin d → Matrix (Fin a) (Fin a) (Om l) := fun i => (B i : Matrix (Fin a) (Fin a) (Om l))
  have hrepr : ∀ x : M, ∑ i, zOm l (B.repr x i) • b i = x := by
    intro x
    have := congrArg Subtype.val (B.sum_repr x)
    rw [Submodule.coe_sum] at this
    simpa [b, hsm] using this
  have h1M : (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ M := Submodule.subset_span ⟨1, by simp [v]⟩
  let e : Fin d → ℤ_[l] := fun i => B.repr ⟨1, h1M⟩ i
  have hreads : Reads ρ r b e := by
    refine ⟨fun g j => ?_, ?_⟩
    · simp_rw [hρ]
      rw [hrepr]
      rfl
    · exact hrepr ⟨1, h1M⟩

  have hliZ : LinearIndependent ℤ_[l] b := B.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent ℚ_[l] b := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 hliZ
  refine ⟨d, ρ, b, e, ?_, hreads, hli, fun i => ?_⟩
  rotate_left
  · obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 (B i).2
    refine ⟨f, ?_⟩
    show (B i : Matrix (Fin a) (Fin a) (Om l)) = _
    rw [← hf]
    simp [Finsupp.sum, hsm, v]

  let Wq := Submodule.span ℚ_[l] (Set.range b)
  let Bq : Module.Basis (Fin d) ℚ_[l] Wq := Module.Basis.span hli
  haveI : FiniteDimensional ℚ_[l] Wq := Module.Finite.of_basis Bq
  have hmemW : ∀ x : M, (x : Matrix (Fin a) (Fin a) (Om l)) ∈ Wq := by
    intro x
    rw [← hrepr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsm, hsq]
    exact Wq.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcoord : ∀ x : M, ∀ i, ((B.repr x i : ℤ_[l]) : ℚ_[l]) = Bq.repr ⟨x, hmemW x⟩ i := by
    intro x i
    have hx : (⟨x, hmemW x⟩ : Wq) = ∑ k, ((B.repr x k : ℤ_[l]) : ℚ_[l]) • Bq k := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      conv_lhs => rw [← hrepr x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul, Module.Basis.span_apply, ← hsm, hsq]
    rw [hx, Module.Basis.repr_sum_self]
  have hcv : Continuous v := Units.continuous_val.comp hr
  have hval : Continuous fun g => (ρ g).val := by
    refine continuous_matrix fun i j => ?_
    have : (fun g => (((ρ g).val i j : ℤ_[l]) : ℚ_[l])) = fun g => Bq.coord i ⟨v g * b j, hmemW (Lm g (B j))⟩ := by
      funext g
      rw [hρ, hcoord]
      rfl
    have hcq : Continuous (fun g => (((ρ g).val i j : ℤ_[l]) : ℚ_[l])) := by
      rw [this]
      refine (LinearMap.continuous_of_finiteDimensional (Bq.coord i)).comp ?_
      exact (hcv.mul continuous_const).subtype_mk _
    exact continuous_induced_rng.2 hcq
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun g => ((ρ g)⁻¹ : GL (Fin d) ℤ_[l]).val) = (fun g => (ρ g).val) ∘ fun g => g⁻¹ := by
    funext g; simp [map_inv]
  rw [this]
  exact hval.comp continuous_inv

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivialCocycleCrystallinePeriodData
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem wseed_of_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (s : Seed bk d ρ τ), ∃ s' : WSeed bk d ρ τ, ∀ g, s'.κ g = 1 := by
  intro l _ K bk τ _ d ρ s
  refine ⟨{ s with κ := fun _ => 1, gal := ?_, fix := fun _ _ => rfl, nopole := ?_, log := ?_ }, fun _ => rfl⟩
  · intro g G hG
    rw [Matrix.mul_one]
    exact s.gal g G hG
  · intro g G hG i j
    obtain ⟨k, hk⟩ := s.nopole bk.ι ((ainfHom K g).comp bk.ι)
    have h1 := map_dvd bk.iA (hk i j)
    have hX : (s.X.map bk.iS).map G = s.X.map (fun x => bk.iA (Per.σA (g : GQ l) (bk.ev x))) := by
      ext a b
      simp only [Matrix.map_apply, BK.iS, RingHom.comp_apply]
      exact hG.ext _
    have hu : IsUnit (bk.iA ((l : Ainf l) ^ k)) := by
      rw [map_pow, map_natCast]
      exact (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k
    change bk.iA ((bk.ev bk.E) ^ (2 * s.N)) ∣ bk.iA ((l : Ainf l) ^ k * (s.X'.map bk.ev * s.X.map (fun x => Per.σA (g : GQ l) (bk.ev x))) i j) at h1
    rw [map_mul] at h1
    rw [Matrix.mul_one, hX]
    have h2 := (hu.dvd_mul_left).1 h1
    convert h2 using 1
    · simp only [BK.iS, RingHom.comp_apply, map_pow]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, BK.iS, RingHom.comp_apply]
  · intro m
    refine ⟨0, 1, fun i j => by simp, fun g G hG i j => ?_⟩
    simp [Matrix.map_one]

end GlobalTheory.BKLim
end
end

