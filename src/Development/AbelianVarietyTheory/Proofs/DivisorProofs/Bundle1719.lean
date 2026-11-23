module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.SatWordAt

open GlobalTheory.LFun Formalism.UG

theorem esymm_add (A B : Multiset ℂ) (j : ℕ) :
    (A + B).esymm j = ∑ i ∈ Finset.HasAntidiagonal.antidiagonal j, A.esymm i.1 * B.esymm i.2 := by
  induction A using Multiset.induction_on generalizing j with
  | empty =>
    rw [zero_add, Finset.sum_eq_single (0, j)]
    · simp [Multiset.esymm]
    · rintro ⟨a, b⟩ hab hne
      have hab' : a + b = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
      obtain _ | a := a
      · exact absurd (by simp [← hab']) hne
      · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
        simp
    · simp
  | cons a A ih =>
    have hrec : ∀ (s : Multiset ℂ) (k : ℕ), (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := fun s k => by
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
    have h0 : ∀ s : Multiset ℂ, s.esymm 0 = 1 := fun s => by simp [Multiset.esymm]
    obtain _ | j := j
    · simp [h0]
    · rw [Multiset.cons_add, hrec, ih, ih, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
      simp only [hrec, h0, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]

theorem satEig_add {q r s N : ℕ} (hq : q ≠ 0) (h : r + s = N) {C B : Multiset ℂˣ} (hC : C.card = r) (hB : B.card = s) (j : ℕ) :
    satEig q N (C + B) j = ∑ i ∈ (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
      (q : ℂ) ^ (((j : ℂ) * (N - j) - i.1 * (r - i.1) - i.2 * (s - i.2)) / 2) * (satEig q r C i.1 * satEig q s B i.2) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hz : ∀ (A : Multiset ℂˣ) (k : ℕ), A.card < k → (A.map fun b : ℂˣ => (b : ℂ)).esymm k = 0 := fun A k hk => by
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hk)]
    simp
  rw [satEig, Multiset.map_add (f := _), esymm_add, Finset.mul_sum]
  symm
  refine Finset.sum_subset_zero_on_sdiff (fun i hi => ?_) (fun i hi => ?_) fun i hi => ?_
  · exact Finset.HasAntidiagonal.mem_antidiagonal.2 (Finset.mem_filter.1 hi).2
  · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
    have h3 := Finset.HasAntidiagonal.mem_antidiagonal.1 h1
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, h3, and_true, not_and_or, not_lt] at h2
    rcases h2 with h2 | h2
    · rw [hz C _ (by omega)]; simp
    · rw [hz B _ (by omega)]; simp
  · simp only [satEig]
    have e : ((j : ℂ) * (N - j)) / 2 = ((j : ℂ) * (N - j) - i.1 * (r - i.1) - i.2 * (s - i.2)) / 2 +
      (i.1 * (r - i.1)) / 2 + (i.2 * (s - i.2)) / 2 := by ring
    rw [e, Complex.cpow_add _ _ hq', Complex.cpow_add _ _ hq']
    ring

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {v : HeightOneSpectrum (𝓞 E)} {N r s : ℕ}

section Lin

variable {m : ℕ} {u : List (Letter E)} {f : Vec u} {h : wsize u + m = N}

end Lin

variable {ϖ : v.adicCompletion E}


end GlobalTheory.ResW.SatWordAt

namespace GlobalTheory.ResW

end GlobalTheory.ResW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
section
noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F]

theorem hasOp_of_symplectic (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (ha : aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0) : HasOp ψ a :=
  _root_.GlobalTheory.SpGen.symplectic_generated_levi_lower_weyl F κ (HasOp ψ) (fun _ _ => HasOp.mul) (GlobalTheory.T.hasRationalWeilOperator_leviBlock F ψ κ) (_root_.GlobalTheory.RatWeilUnip.hasOp_unip F ψ hψ κ) (_root_.GlobalTheory.WeylFourier.weyl_hasOp F hF ψ hψ κ) a ha

section Pure

variable {κ : Type} [Fintype κ]

theorem pure_mem (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ.1 hφ.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ.1 hφ.2⟩, rfl⟩

theorem schA_le {N : Submodule ℂ ((κ → AF F) → ℂ)} (h : ∀ f φ, IsFam φ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N) : schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ ⟨hφ, hs⟩

theorem IsFam.finite {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have h : ∀ᶠ v in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (x i).2.2
  refine (eventually_cofinite.1 ?_)
  filter_upwards [h, hφ.2] with v h1 h2
  rw [h2, ind, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h1)]
  rfl

theorem pure_smul (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (m : Pl F → ℂ) (h0 : ∀ v, m v ≠ 0)
    (h1 : ∀ᶠ v in cofinite, m v = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ᶠ v, m v) • f) (fun v => (m v)⁻¹ • φ v) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  have hm : (Function.mulSupport m).Finite := eventually_cofinite.1 h1
  have hm' : (Function.mulSupport fun v => (m v)⁻¹).Finite := hm.subset fun v hv h => hv (by simp only [h, inv_one])
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  rw [finprod_mul_distrib hm' (hφ.finite x)]
  have : (∏ᶠ v, m v) * ∏ᶠ v, (m v)⁻¹ = 1 := by
    rw [← finprod_mul_distrib hm hm']
    exact finprod_eq_one_of_forall_eq_one fun v => mul_inv_cancel₀ (h0 v)
  linear_combination (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) * this

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) :
    ((κ → R) → ℂ) →ₗ[ℂ] (κ → R) → ℂ where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' a φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ}
  {ei : SInf F κ →L[ℂ] SInf F κ} {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ}

theorem IsOp.maps (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ := fun _ hΦ =>
  schA_le (N := (schA F κ).comap e) (fun f φ hφ => by
    rw [Submodule.mem_comap, (h.2.2.2.2.2 f φ hφ).1]
    exact pure_mem _ (h.isFam hφ)) hΦ

theorem IsOp.Heisenberg₂ (h : IsOp ψ a e c ei ev) (w : (κ → AF F) × (κ → AF F)) :
    ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (act (a.map (algebraMap F (AF F))) w) (e Φ) := fun _ hΦ =>
  schA_le (N := LinearMap.eqLocus (e ∘ₗ schrL ψ w) (schrL ψ (act (a.map (algebraMap F (AF F))) w) ∘ₗ e))
    (fun f φ hφ => (h.2.2.2.2.2 f φ hφ).2.1 w) hΦ

theorem IsOp.theta (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := fun _ hΦ =>
  (schA_le (N := {
      carrier := {Φ | Φ ∈ schA F κ ∧ thetaSum F (e Φ) = c * thetaSum F Φ}
      zero_mem' := ⟨zero_mem _, by simp [thetaSum]⟩
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        rw [map_add (f := _), thetaSum_add F (h.maps _ hx.1) (h.maps _ hy.1), thetaSum_add F hx.1 hy.1, hx.2, hy.2, mul_add]⟩
      smul_mem' := fun r x hx => ⟨Submodule.smul_mem _ r hx.1, by
        rw [map_smul, thetaSum_smul, thetaSum_smul, hx.2, mul_left_comm]⟩ })
    (fun f φ hφ => ⟨pure_mem f hφ, (h.2.2.2.2.2 f φ hφ).2.2⟩) hΦ).2

theorem IsOp.bijOn (hψ : IsStd ψ) (h : IsOp ψ a e c ei ev) : Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) := by
  classical
  refine ⟨h.maps, fun Φ hΦ Φ' hΦ' he => ?_, ?_⟩
  · have hd : Φ - Φ' ∈ schA F κ := sub_mem hΦ hΦ'
    refine sub_eq_zero.1 (_root_.GlobalTheory.ThetaInj.main F ψ hψ κ _ hd fun w => ?_)
    have h1 := h.theta _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w _ hd)
    rw [h.Heisenberg₂ w _ hd, map_sub, he, sub_self, show schr ψ _ (0 : (κ → AF F) → ℂ) = 0 from (schrL ψ _).map_zero] at h1
    exact (mul_eq_zero.1 (h1.symm.trans (by simp [thetaSum]))).resolve_left h.1
  · refine schA_le (N := (schA F κ).map e) fun g φ' hφ' => ?_
    obtain ⟨f, rfl⟩ := h.2.1 g
    have key : ∀ v, ∃ p ∈ SB (κ → Fv F v), ev v p = φ' v ∧ (φ' v = ind κ v → ev v (ind κ v) = ind κ v → p = ind κ v) := by
      intro v
      by_cases hv : φ' v = ind κ v ∧ ev v (ind κ v) = ind κ v
      · exact ⟨ind κ v, hv.1 ▸ hφ'.1 v, hv.2.trans hv.1.symm, fun _ _ => rfl⟩
      · obtain ⟨p, hp, hp'⟩ := (h.2.2.1 v).surjOn (hφ'.1 v)
        exact ⟨p, hp, hp', fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
    choose φ h1 h2 h3 using key
    have hφ : IsFam φ := ⟨h1, by filter_upwards [hφ'.2, h.2.2.2.2.1] with v p q using h3 v p q⟩
    exact ⟨_, pure_mem f hφ, by rw [(h.2.2.2.2.2 f φ hφ).1]; simp only [h2]⟩

end Pure

section Vac

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem schr_of_acts (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB _) {χ : ℂ} (h : Acts (evFin F v) (M.co.rho ψ γ) φ (χ • φ)) :
    schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ = χ • φ := by
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v φ hφ
  funext ξ
  have := GlobalTheory.LatVac.heis_at_local_identity v M.co ψ γ φ χ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) h r hr x₀ hx₀ ξ
  rw [schr, invOf_eq_inv]
  exact this

theorem vac_line (B : Base F E) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (M : Model σ X W) (v : Pl F) {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (h : M.IsVac B.ψ v φ) (h' : M.IsVac B.ψ v φ') :
    ∃ m : ℂ, φ' = m • φ := by
  classical
  obtain ⟨hφ, hφ0, θ, hθ, hA⟩ := h
  obtain ⟨hφ', -, θ', hθ', hA'⟩ := h'
  have hAt := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  let χ : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin n × Fin d → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • f)) →
      ∀ l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l := AddSubgroup.mem_map.mp hl
    have key := congrFun (schr_of_acts M B.ψ h.choose_spec.1 hf (hA _ h.choose_spec.1)) ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2, schr, invOf_eq_inv] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat.toIsLattice hW.lat.toIsLattice
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ hAt (GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace F E σ B n d X W r s r' s' hB hX hW v)
  have hfill := GlobalTheory.T.self_dual_lattice_invariant_vector F v _ (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hB.std _) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) _ c hc0 hsd
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  refine GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) _ χ φ φ' (loc φ hφ hA) (loc φ' hφ' fun γ hγ => ?_) hφ0 hfill
  have heq := GlobalTheory.T.vacuum_eigenvalue_theta_independent F E σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ
  change B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) at heq
  rw [heq]
  exact hA' γ hγ

theorem IsOp.isVac {ψ : AddChar (AF F) ℂ} {a e c ei ev} (h : IsOp (κ := Fin n × Fin d) ψ a e c ei ev) (M M₁ : Model σ X W)
    (hco : ∀ u, M₁.co.e u = act (a.map (algebraMap F (AF F))) (M.co.e u)) (v : Pl F) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : M.IsVac ψ v φ) : M₁.IsVac ψ v (ev v φ) := by
  obtain ⟨h1, h0, θ, hθ, hA⟩ := hφ
  refine ⟨(h.2.2.1 v).mapsTo h1, fun h2 => h0 ((h.2.2.1 v).injOn h1 (zero_mem _) (h2.trans (map_zero _).symm)), θ, hθ,
    fun γ hγ => ?_⟩
  have e1 : GlobalTheory.LatVac.locCo M₁.co v γ = act (a.map (algebraMap F (Fv F v))) (GlobalTheory.LatVac.locCo M.co v γ) := by
    have e2 : ∀ k, evFin F v ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e γ).1 (M.co.e γ).2) k) =
        (a.map (algebraMap F (Fv F v)) *ᵥ Sum.elim (GlobalTheory.LatVac.locCo M.co v γ).1 (GlobalTheory.LatVac.locCo M.co v γ).2) k := fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases j <;> rfl
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show evFin F v ((M₁.co.e γ).1 k) = _
      rw [hco]; exact e2 _
    · show evFin F v ((M₁.co.e γ).2 k) = _
      rw [hco]; exact e2 _
  have e3 := GlobalTheory.VacBridge.rho_acts_locCo M₁.co ψ v γ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) (ev v φ)
  rwa [e1, ← h.2.2.2.1 v _ φ h1, schr_of_acts M ψ hγ h1 (hA γ hγ), map_smul] at e3

end Vac

theorem exists_intertwiner : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → (∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr)) → ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), c ≠ 0 ∧ IsEv B M M₁ 1 1 ∅ e ∧ Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M M₁ r s r' s' hB hX hW hM hM₁ a ha hco
  obtain ⟨e, c, ei, ev, h⟩ := hasOp_of_symplectic hB.cm.1 hB.std a ha
  have key : ∀ v, ∃ m : ℂ, m ≠ 0 ∧ ev v (M.vac v) = m • M₁.vac v ∧ (ev v (M.vac v) = M₁.vac v → m = 1) := fun v => by
    by_cases hv : ev v (M.vac v) = M₁.vac v
    · exact ⟨1, one_ne_zero, by rw [hv, one_smul], fun _ => rfl⟩
    · have h1 := h.isVac M M₁ hco v (hM.vac v)
      obtain ⟨m, hm⟩ := vac_line B hB hX hW M₁ v (hM₁.vac v) h1
      exact ⟨m, fun h0 => h1.2.1 (by rw [hm, h0, zero_smul]), hm, fun h2 => absurd h2 hv⟩
  choose m hm0 hm hm1 using key
  have hmc : ∀ᶠ v in cofinite, m v = 1 := by
    filter_upwards [hM.std, hM₁.std, h.2.2.2.2.1] with v h1 h2 h3
    exact hm1 v (by rw [h1, h2]; exact h3)
  have hP : (∏ᶠ v, m v) ≠ 0 := finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hm0
  refine ⟨e, c, h.1, ⟨h.maps, fun z Φ hΦ => ?_, fun u hu => absurd hu (Set.notMem_empty u),
    (∏ᶠ v, m v) • ei, fun v => (m v)⁻¹ • ev v, fun h0 => ?_, fun v => ⟨?_, ?_⟩, fun f φ h1 h2 => ?_⟩, h.bijOn hB.std, h.theta⟩
  · have h1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := fun k => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Darboux.rho, Darboux.rho, hco]
    exact h.Heisenberg₂ _ Φ hΦ
  · have h1 : ei = 0 := (smul_eq_zero.1 h0).resolve_left hP
    obtain ⟨Φ, hΦ, hΦ0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin n × Fin d)
    have h2 : schA F (Fin n × Fin d) ≤ ⊥ := schA_le fun g φ _ => by
      obtain ⟨f, rfl⟩ := h.2.1 g
      rw [h1, Submodule.mem_bot]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    exact hΦ0 (by rw [(Submodule.mem_bot ℂ).1 (h2 hΦ)]; rfl)
  · rw [LinearMap.smul_apply, hm, smul_smul, inv_mul_cancel₀ (hm0 v), one_smul]
  · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hm0 v))]
    exact SetLike.coe_injective ((Submodule.map_coe _ _).trans (h.2.2.1 v).image_eq)
  · have hφ : IsFam φ := ⟨h1, by filter_upwards [h2, hM.std] with v p q using p.trans q⟩
    rw [(h.2.2.2.2.2 f φ hφ).1, ← pure_smul (ei f) (h.isFam hφ) m hm0 hmc]
    rfl

end GlobalTheory.RatWeilOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBasePStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_unrAt_of_under_eq_v0 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = G.pl.v0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace | exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace | (intros; apply GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelFinitePointMemSpanRationalFormLifts
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSpanCore

open GlobalTheory.KernelSpan


set_option maxHeartbeats 1000000 in
theorem kernel_mem_span_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ h ∈ GfC (Vc D i), ∀ (w : (R.cV i).W) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (fun g : GA D (Wc D i) => thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w))) ∈ Submodule.span ℂ (Set.range fun x₀ : A.fam.amb.FL i t => (R.thF i t (jVx R i t x₀) (fun ρ => u ρ) : GA D (Wc D i) → ℂ)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t hV h hh w u
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  refine (GlobalTheory.SplitReps.exists_bad R t one_pos).elim fun bad hbad => ?_
  refine (GlobalTheory.SplitReps.exists_split_system R i t le_rfl (by simp) hbad.1
    (fun k _ hk => GlobalTheory.SplitReps.fin_mem_levJ R i (hR.lev.βV i) t hbad.2.2 k hk) one_pos).elim fun m hm =>
    hm.elim fun ys hys => ?_
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := exists_integral (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) (Fin m) ys hys.2.1 hys.2.2 (fun k => (hys.1 k).1) hh w
  refine key.elim fun f hf => hf.2.elim fun a ha => ?_
  have hr := (hR.models.HV i t).2.1
  have hf' : f ∈ LinearMap.range (R.HV i t).e := hr.ge hf.1
  refine hf'.elim fun y hy => ?_
  have h0 : (R.B.L i t).pres.ExtBij := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1
  have he : ∀ x, (R.HV i t).e (jVx R i t x) = (R.B.L i t).pres.extL x := hR.models.jV i t
  have hsp : Submodule.span ℂ (Set.range (jVx R i t)) = ⊤ :=
    span_eq_top_of_model (R.HV i t).e (hR.models.HV i t).1 (jVx R i t) _ he (h0.2.trans hr.symm)
  let T : (R.HV i t).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun y => R.thF i t y (fun ρ => u ρ)
      map_add' := fun y y' => by rw [map_add (f := _)]; rfl
      map_smul' := fun c y => by rw [map_smul]; rfl }
  refine mem_span_of_linear (jVx R i t) hsp T y a ha.1 _ (funext fun g => ?_)
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  have h3 := ha.2 g
  rw [← hy] at h3
  exact h1.trans (h2.trans (Eq.trans rfl h3))

end GlobalTheory.KernelSpanCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformAdelicSchwartzHasFiniteLevelCMStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  first | exact @GlobalTheory.ThetaLevelF.thetaTr_levelF | exact GlobalTheory.ThetaLevelF.thetaTr_levelF | (intros; apply GlobalTheory.ThetaLevelF.thetaTr_levelF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformHasLevelCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLevelCM

theorem thetaTr_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 →
              Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) =
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ hψ JA JB ξ hA hJB κ _ co hco φ hφ
  exact GlobalTheory.ThetaLevelF.thetaTr_levelF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hJB κ co hco φ hφ

end GlobalTheory.ThetaLevelCM
end

