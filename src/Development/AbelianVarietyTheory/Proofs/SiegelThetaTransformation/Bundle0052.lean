module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TensLatMove

variable {D : D7}

def emb (D : D7) : AfE D →ₗ[D.host.F] AE D :=
  TensorProduct.map (GlobalTheory.AdelicLatMove.finIncl D) LinearMap.id

theorem emb_tmul (e : D.host.E) (α : Af D.host.F) :
    emb D (α ⊗ₜ[D.host.F] e) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e := rfl

theorem finPart_tmul (x : AF D.host.F) (e : D.host.E) :
    Formalism.L2.Theta.finPart D (x ⊗ₜ[D.host.F] e) = (sndA D.host.F x) ⊗ₜ[D.host.F] e := rfl

theorem emb_mul (a : AE D) (x : AfE D) : emb D (Formalism.L2.Theta.finPart D a * x) = a * emb D x := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add (f := _), add_mul, ha, hb]
  | tmul y e =>
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add (f := _), mul_add, ha, hb]
    | tmul α f =>
      rw [finPart_tmul, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, emb_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      exact Prod.ext (mul_zero y.1).symm rfl

def outer (S T : HSp D) (v : Fin S.rank → AfE D) (u : Fin T.rank → AfE D) : WO S T :=
  Matrix.of fun a k => emb D (u a * v k)

def outerHom (S T : HSp D) : (Fin S.rank → AfE D) →+ (Fin T.rank → AfE D) →+ WO S T :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun u => outer S T v u) (fun u u' => by
      ext i j
      simp only [outer, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul]))
    (fun v v' => AddMonoidHom.ext fun u => by
      ext i j
      simp only [outer, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Matrix.of_apply, Matrix.add_apply,
        Pi.add_apply, map_add, mul_add])

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (hβ : β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) :
    α * β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem intAf_one : (1 : Af D.host.F) ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem outer_pure (S T : HSp D) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (α β : Af D.host.F) :
    outer S T (fun i => α ⊗ₜ[D.host.F] s i) (fun i => β ⊗ₜ[D.host.F] t i) =
      Matrix.of fun a k => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] (vecMulVec s t k a) := by
  ext a k
  simp only [outer, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, vecMulVec_apply, mul_comm (t a)]

theorem outer_mem (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank)
    (v : Fin S.rank → AfE D) (hv : v ∈ hatV Λ) (u : Fin T.rank → AfE D) (hu : u ∈ hatV L) :
    outer S T v u ∈ hatA S T (tens Λ L) := by
  change outerHom S T v u ∈ _
  induction hv using AddSubgroup.closure_induction with
  | mem s hs =>
    induction hu using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      apply AddSubgroup.subset_closure
      exact ⟨β * α, intAf_mul hβ hα, vecMulVec x y, AddSubgroup.subset_closure ⟨x, hx, y, hy, rfl⟩,
        outer_pure S T x y α β⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem hatA_le (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank) (K : AddSubgroup (WO S T))
    (hK : ∀ v ∈ hatV Λ, ∀ u ∈ hatV L, outer S T v u ∈ K) : hatA S T (tens Λ L) ≤ K := by
  rw [hatA, AddSubgroup.closure_le]
  rintro _ ⟨α, hα, y, hy, rfl⟩
  change _ ∈ K
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hy
    have e := outer_pure S T s t 1 α
    rw [mul_one] at e
    rw [← e]
    exact hK _ (AddSubgroup.subset_closure ⟨1, intAf_one, s, hs, rfl⟩) _
      (AddSubgroup.subset_closure ⟨α, hα, t, ht, rfl⟩)
  | zero =>
    convert zero_mem K using 1
    ext a k
    simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext a k
    simp [TensorProduct.tmul_add]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext a k
    simp [TensorProduct.tmul_neg]

theorem actO_outer (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (v : Fin S.rank → AfE D)
    (u : Fin T.rank → AfE D) :
    actO S T h g (outer S T v u) = outer S T (fmtC S h *ᵥ v) (fmt T g *ᵥ u) := by
  have key := GlobalTheory.AdelicLatMove.gram_mul_inv S h
  have h1 : S.gram.map (incA D) = 1 := by rw [hS, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1, Matrix.one_mul, Matrix.mul_one] at key
  ext i j
  simp only [actO, key, outer, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← emb_mul, ← map_sum, mul_comm (emb D _)]
  congr 1
  simp only [fmt, fmtC, Formalism.L2.Theta.cM, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

def actHom (S T : HSp D) (h : GA D S) (g : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T h g) (fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul])

theorem mem_hatA_iff (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank)
    (L L' : Lt D.host.E T.rank) (h1 : IsMov (fmtC S h) Λ Λ') (h2 : IsMov (fmt T g) L L') (u : WO S T) :
    u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀ := by
  constructor
  · intro hu
    have := hatA_le S T Λ' L' ((hatA S T (tens Λ L)).map (actHom S T h g)) (fun v hv w hw => by
      obtain ⟨v₀, hv₀, rfl⟩ := (h1 v).1 hv
      obtain ⟨w₀, hw₀, rfl⟩ := (h2 w).1 hw
      exact ⟨_, outer_mem S T Λ L v₀ hv₀ w₀ hw₀, actO_outer S T hS h g v₀ w₀⟩) hu
    obtain ⟨u₀, hu₀, e⟩ := this
    exact ⟨u₀, hu₀, e.symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    refine hatA_le S T Λ L ((hatA S T (tens Λ' L')).comap (actHom S T h g)) (fun v hv w hw => ?_) hu
    change actO S T h g _ ∈ hatA S T (tens Λ' L')
    rw [actO_outer S T hS]
    exact outer_mem S T Λ' L' _ ((h1 _).2 ⟨v, hv, rfl⟩) _ ((h2 _).2 ⟨w, hw, rfl⟩)

theorem hatA_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank), IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → (∀ u, u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀) ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ f, C.IsTh f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) := by
  intro D S T C h g Λ Λ' L L' h1 h2
  have hΛ := mem_hatA_iff S T C.m.gS h g Λ Λ' L L' h1 h2
  refine ⟨hΛ, fun om hW f hth hlat => ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hW.om_heis h g _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e h⁻¹ g⁻¹ hh
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hW.om_heis h g _ f hth, hlat.2 e he u₀ hu₀ h0]

end GlobalTheory.TensLatMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StableFormsEqSumThetaSeriesFreeLowerRows
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

private theorem thP_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ}
    (X : Data E r) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (φ : SW.TF n g) (c : ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    (x : Frame X.Ψ r) : thP X hr bas idx φ (c • P) x = c * thP X hr bas idx φ P x := by
  unfold thP
  by_cases hc : c = 0
  · subst hc
    simp [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv]
  · simp only [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_smul_eq hc,
      MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => mul_assoc _ _ _

theorem GlobalTheory.Dict.stabForms_eq_sum_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ i, L i ∈ D.lats) → (∀ i i', ∀ ga ∈ D.grp, mapL ga (L i) = L i' → i = i') → (∀ i, ∀ ga ∈ D.grp, mapL ga (L i) = L i → mu ga (L i) = 1) → (∀ i, IsStabForm X D.grp (L i) (wtOf X hr k k' n) (Q i)) → ∃ (m : ℕ) (Λ : Fin m → Lt E n) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), (∀ j, Λ j ∈ Vset E n M ∧ P j ∈ Harm.rowHighest ℂ k k') ∧ ∀ i, ∀ x ∈ X.dom, Q i x = ∑ j, thP X hr bas idx (phiF bas D 𝔐 hn v₀ (L i) (Λ j)) (P j) x := by
  intro E _ _ _ r X g q0 hr bas idx n hS hE hn4 D hn M 𝔐 𝔍 hM hMm hmf hcop v₀ hv mu hmu k k' Jx _ L Q
    hL hinj hfix hQ

  obtain ⟨hnorm, -, hcoc⟩ := _root_.GlobalTheory.Dict.vac_multiplier_cocycle E r X g bas idx n hS hE D v₀ hv mu hmu

  have hsys := _root_.GlobalTheory.SW.isSystem_level E r X g bas idx n hS hE hn4 D hn M hM hMm v₀ hv mu hmu

  obtain ⟨F, hF, hFL⟩ := _root_.GlobalTheory.Dict.exists_form_extend E r X D.grp D.lats mu (wtOf X hr k k' n) Jx L Q hsys.un
    (fun ga hga L' hL' => ⟨hsys.stab ga hga L' hL', hnorm ga hga L' hL'⟩) hcoc hL hinj hfix hQ

  obtain ⟨m, Λ, P, a, hΛP, hFsum⟩ :=
    GlobalTheory.SW.level_theta_span E r X g q0 hr bas idx n hS hE hn4 D hn M hM hMm v₀ hv mu hmu k k' F hF

  have h97 := fun j => _root_.GlobalTheory.Dict.DiagFree.thP_phi_eq_thP_phiF E r X g q0 hr bas idx n hS hE D hn M 𝔐 𝔍 hM hMm hmf hcop v₀ hv
    k k' (Λ j) (hΛP j).1 (P j) (hΛP j).2
  choose Λ' hΛ' P' hP' heq using h97
  refine ⟨m, Λ', fun j => a j • P' j, fun j => ⟨hΛ' j, Submodule.smul_mem _ _ (hP' j)⟩, ?_⟩
  intro i x hx
  rw [← hFL i x hx, hFsum (L i) (hL i) x hx]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [heq j (L i) (hL i) x hx, thP_smul']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
section
noncomputable section

namespace GlobalTheory.Ker.WeakMove

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hom : IsWeak ψ S T om) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {L L' : ℝ →+ WO S T} (hL : IsRealDir T S L) (hL' : IsRealDir T S L') (hLL : ∀ t, L' t = actO S T g h (L t))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := i1; have := i2; have := i3; have := i4; have := i5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable (ratL T S) := countable_of_Lindelof_of_discrete
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have hF : IsThetaFunO ψ S T (om (g, h) f) := hom.om_pres _ _ hf
  have hd : IsThetaFunO ψ S T (dLine ψ S T L f) := theta_dLine hθ hψ hL hf
  have hd' : IsThetaFunO ψ S T (dLine ψ S T L' (om (g, h) f)) := theta_dLine hθ hψ hL' hF
  have hδ : IsThetaFunO ψ S T (om (g, h) (dLine ψ S T L f) - dLine ψ S T L' (om (g, h) f)) :=
    theta_sub (hom.om_pres _ _ hd) hd'
  obtain ⟨C₁, hC₁⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C₂, hC₂⟩ := quotient_bound hθ hψ hL' hF
  have hν : (μ.restrict 𝓕) Set.univ = 1 := by rw [Measure.restrict_apply_univ]; exact h1
  have h0 : ∫⁻ w, ‖(om (g, h) (dLine ψ S T L f) - dLine ψ S T L' (om (g, h) f)) w‖ₑ ^ 2 ∂(μ.restrict 𝓕) = 0 := by
    refine lintegral_eq_zero_of_approx (μ.restrict 𝓕) hν _ C₁ C₂ fun t ht => ?_
    have hq : IsThetaFunO ψ S T ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)) :=
      theta_smul _ (theta_sub (theta_heisO_real hθ hψ (hL.2 t) hf) hf)
    have hom_q : om (g, h) ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)) =
        (t : ℂ)⁻¹ • (heisO ψ S T (L' t) (om (g, h) f) - om (g, h) f) := by
      rw [map_smul, map_sub, hom.om_heis g h (L t) f hf, ← hLL t]
    refine ⟨om (g, h) (dLine ψ S T L f - (t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)),
      dLine ψ S T L' (om (g, h) f) - om (g, h) ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)),
      dLine ψ S T L f - (t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f), ?_, ?_, ?_, ?_⟩
    · rw [map_sub]; abel
    · exact hom.om_unit μ 𝓕 hμ h𝓕 _ _ (theta_sub hd hq)
    · intro w
      rw [Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply]
      exact hC₁ t ht w
    · intro w
      rw [hom_q, Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply]
      exact hC₂ t ht w
  exact sub_eq_zero.mp
    (eq_zero_of_lintegral_eq_zero (ratL T S) μ 𝓕 h𝓕 _ hδ.cont (theta_norm_periodic hψ hδ) h0)

theorem om_dRho (hom : IsWeak ψ S T om) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) := by
  rw [dRho_eq_dLine, dRho_eq_dLine]
  exact GlobalTheory.Ker.WeakMove.om_dLine hom hψ hθ g h (isRealDir_lineAt hθ τ z) (isRealDir_lineAt hθ τ _)
    (fun t => lineAt_move hθ g h τ z t) hf

theorem sB_mvB (C : Ctx S T) (g : GA D T) (B : C.Bas) (τ : D.what₂.Tau) :
    C.sB (C.mvB g B) τ * compAt C.θ τ (mt T g) = compAt C.θ τ (mt T g) * C.sB B τ := by
  have h1 : compAt C.θ τ (mt T g) * compAt C.θ τ (mt T g⁻¹) = 1 := compAt_mt_mul_inv τ g
  have h2 : (compAt C.θ τ (mt T g))⁻¹ * compAt C.θ τ (mt T g) = 1 := by
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h1)
  simp only [Ctx.sB, Ctx.mvB, Matrix.mul_inv_rev, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem isFock_om (C : Ctx S T) (hom : IsWeak C.ψ S T om) (h : GA D S) (g : GA D T) {f : WO S T → ℂ} (hf : C.IsTh f)
    (B : C.Bas) (hB : C.IsFock B f) : C.IsFock (C.mvB g B) (om (h, g) f) := by
  intro τ z
  have hM : compAt C.θ τ (mt T g) * compAt C.θ τ (mt T g⁻¹) = 1 := compAt_mt_mul_inv τ g
  have hG : compAt C.θ τ (mt S h) * compAt C.θ τ (mt S h⁻¹) = 1 := compAt_mt_mul_inv τ h
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin T.rank) (Fin S.rank) ℂ, z = compAt C.θ τ (mt T g) * z₀ * compAt C.θ τ (mt S h⁻¹) := by
    refine ⟨compAt C.θ τ (mt T g⁻¹) * z * compAt C.θ τ (mt S h), ?_⟩
    simp only [Matrix.mul_assoc, hG, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hM, Matrix.one_mul]
  have key := hB τ z₀
  have hc : cplxO 1 (C.sB (C.mvB g B) τ) (compAt C.θ τ (mt T g) * z₀ * compAt C.θ τ (mt S h⁻¹)) =
      compAt C.θ τ (mt T g) * cplxO 1 (C.sB B τ) z₀ * compAt C.θ τ (mt S h⁻¹) :=
    cplxO_move hG (by rw [Matrix.one_mul, Matrix.mul_one]) (sB_mvB C g B τ) z₀
  unfold annih at key ⊢
  rw [hc, ← GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ z₀ hf,
    ← GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ _ hf, ← map_smul, ← map_add, key, map_zero]

theorem om_fvec (C : Ctx S T) (hom : IsWeak C.ψ S T om) (h : GA D S) (g : GA D T) {f : WO S T → ℂ} (hf : C.IsTh f)
    (B : C.Bas) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B))
      (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  unfold Ctx.fvec pureTensorO
  refine (pureTensorL_intertwine (IsThetaFunO C.ψ S T) theta_zero (fun a b ha hb => theta_add ha hb)
    (fun c a ha => theta_smul c ha) _ _ (om (h, g)) ?_ f hf Q).2
  intro k f' hf'
  have hG : compAt C.θ k.1 (mt S h) * compAt C.θ k.1 (mt S h⁻¹) = 1 := compAt_mt_mul_inv k.1 h
  have hu : unitMap (compAt C.θ k.1 (mt S h)) (C.mvB g B k.1) k.2.1 k.2.2 =
      compAt C.θ k.1 (mt T g) * unitMap 1 (B k.1) k.2.1 k.2.2 * compAt C.θ k.1 (mt S h⁻¹) := by
    have := unitMap_move (B := 1) (B' := B k.1) (H := compAt C.θ k.1 (mt T g)) hG k.2.1 k.2.2
    rwa [Matrix.mul_one] at this
  have hc : ∀ z, cplxO 1 (C.sB (C.mvB g B) k.1) (compAt C.θ k.1 (mt T g) * z * compAt C.θ k.1 (mt S h⁻¹)) =
      compAt C.θ k.1 (mt T g) * cplxO 1 (C.sB B k.1) z * compAt C.θ k.1 (mt S h⁻¹) := fun z =>
    cplxO_move hG (by rw [Matrix.one_mul, Matrix.mul_one]) (sB_mvB C g B k.1) z
  unfold aPlusAll aPlus crea
  beta_reduce
  refine ⟨?_, ?_⟩
  · exact theta_smul _ (theta_sub (theta_dRho C.inf C.std _ _ hf') (theta_smul _ (theta_dRho C.inf C.std _ _ hf')))
  · simp only [map_smul, map_sub]
    rw [GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g _ _ hf', GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g _ _ hf',
      hu]
    exact congrArg _ (congrArg _ (congrArg _
      (congrArg (fun z => Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ k.1 z (om (h, g) f')) (hc _).symm)))

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem om_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (h : GA D S) (g : GA D T) f, C.IsTh f → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), om (h, g) (dRho (heisO C.ψ S T) C.θ τ z f) = dRho (heisO C.ψ S T) C.θ τ (compAt C.θ τ (mt T g) * z * compAt C.θ τ (mt S h⁻¹)) (om (h, g) f)) ∧ ∀ B, C.IsB B → (C.IsFock B f → C.IsFock (C.mvB g B) (om (h, g) f)) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B)) (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  intro D S T C om hom h g f hf
  exact ⟨fun τ z => GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ z hf,
    fun B _ => ⟨fun hB => isFock_om C hom h g hf B hB, fun Q => om_fvec C hom h g hf B Q⟩⟩

end

end GlobalTheory.Ker.WeakMove

end
end

