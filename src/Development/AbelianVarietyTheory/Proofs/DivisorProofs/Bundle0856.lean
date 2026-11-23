module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExt

theorem prod_ofFn_eq {X : Type*} [Monoid X] {V : Type*} [AddCommMonoid V] (T : V → X)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_eq T h0 hadd (fun i => w i.succ), Fin.sum_univ_succ, hadd]

theorem lie_ext : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (ρ : W) (t : Fin D.a → (𝓞 D.F →+* W)), (∀ i, t i D.ω = ρ) → ρ ^ 2 - D.tr * ρ + D.nm = 0 → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) → (∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L ρ)) v → ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c) (β (algebraMap W L (t i c))) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i, LieMult (act.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (t i)) D.m) → (∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∀ v : epsPtR (spMap β) ⟶ G, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O D.ω) (β ρ) v → ∃ w : Fin D.a → (epsPtR (spMap β) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) (β (t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k) i, LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m := by
  intro p _ D W L _ _ _ _ _ _ G _ _ hab act ρ t htω hρ hcomax hdisc hgen hrank
  have hsm : Smooth G.hom := hab.smooth
  obtain ⟨n, M, hM⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group W G hsm

  have hT0 : ∀ {X : Type} [Group X] {V : Type} [AddCommMonoid V] (T : V → X),
      (∀ c c', T (c + c') = T c * T c') → T 0 = 1 := fun T h => by
    have := h 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨T₀, hinj₀, -, hadd₀, -, heq₀⟩ := hM W (RingHom.id W)
  have hmap : ∀ X : Matrix (Fin n) (Fin n) W, X.map (RingHom.id W) = X := fun X => by ext; simp
  have hext : ∀ X Y : Matrix (Fin n) (Fin n) W, (∀ c, T₀ (X.mulVec c) = T₀ (Y.mulVec c)) → X = Y := by
    intro X Y h
    ext i j
    have := congrFun (hinj₀ (h (Pi.single j 1))) i
    simpa [Matrix.mulVec_single_one] using this
  let Am : 𝓞 D.F → Matrix (Fin n) (Fin n) W := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have hAm : ∀ c x, T₀ x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T₀ ((Am c).mulVec x) := fun c x => by
    simpa [hmap] using heq₀ _ (act.hom _) x
  let A : 𝓞 D.F →+* Matrix (Fin n) (Fin n) W := RingHom.mk'
    { toFun := Am
      map_one' := hext _ _ fun x => by
        rw [Matrix.one_mulVec, ← hAm, map_one, act.one, Category.comp_id]
      map_mul' := fun c d => hext _ _ fun x => by
        rw [← hAm, map_mul, act.mul, ← Category.assoc, hAm, hAm, Matrix.mulVec_mulVec] }
    (fun c d => hext _ _ fun x => by
      show T₀ ((Am (c + d)).mulVec x) = T₀ ((Am c + Am d).mulVec x)
      rw [← hAm, map_add (f := _), act.add, MonObj.comp_mul, hAm, hAm, ← hadd₀, Matrix.add_mulVec])
  have hA : ∀ c, A c = M (act.act (algebraMap (𝓞 D.F) D.O c)) := fun c => rfl

  have tanT : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (T : (Fin n → R') → (epsPtR (spMap β) ⟶ G)),
      Function.Injective T →
      (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) →
      (∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)) →
      (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) →
      ∀ (c : 𝓞 D.F) (s : R') (x : Fin n → R'),
        IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) s (T x) ↔ ((A c).map β).mulVec x = s • x := by
    intro R' _ β T hinj hscale heq hrange c s x
    have hact : T x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T (((A c).map β).mulVec x) :=
      heq _ (act.hom _) x
    constructor
    · rintro ⟨-, h2⟩
      refine hinj (Over.OverMorphism.ext ?_)
      rw [← hact, h2, hscale]
    · intro hx
      refine ⟨(hrange _).2 ⟨x, rfl⟩, ?_⟩
      rw [hact, hx, hscale]
  have hωroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hβL : (RingHom.id L).comp (algebraMap W L) = algebraMap W L := RingHom.id_comp _
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := GlobalTheory.T.eigenPart_splits_by_idempotent_matrices_domain W L (𝓞 D.F) n D.a A D.ω D.tr D.nm ρ t hωroot hρ htω hcomax hdisc
    (by
      intro v hv
      obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM L ((RingHom.id L).comp (algebraMap W L))
      have tv := (tanT L _ T hinj hscale heq hrange D.ω ((RingHom.id L) (algebraMap W L ρ)) v).2
        (by rw [hβL, RingHom.id_apply]; exact hv)
      obtain ⟨w, hw, hvw⟩ := hgen L (RingHom.id L) (T v) tv
      have hy : ∀ i, ∃ y, w i = T y := fun i => by obtain ⟨y, h⟩ := (hrange _).1 (hw i 0).1; exact ⟨y, h.symm⟩
      choose y hy using hy
      refine ⟨y, fun i c => ?_, ?_⟩
      · have := (tanT L _ T hinj hscale heq hrange c _ (y i)).1 (by rw [← hy]; exact hw i c)
        rwa [hβL, RingHom.id_apply] at this
      · apply hinj
        rw [hvw, ← prod_ofFn_eq T (hT0 T hadd) hadd]
        exact congrArg List.prod (congrArg List.ofFn (funext hy)))
  have hmapsmul : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (s : W) (X : Matrix (Fin n) (Fin n) W),
      (s • X).map β = β s • X.map β := fun R' _ β s X => by ext; simp
  have heig : ∀ (R' : Type) [CommRing R'] (β : W →+* R') i c (x : Fin n → R'),
      ((A c).map β).mulVec (((Q i).map β).mulVec x) = β (t i c) • (((Q i).map β).mulVec x) := by
    intro R' _ β i c x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQ2, hmapsmul, Matrix.smul_mulVec]

  have rk : ∀ (k : Type) [Field k] (β : W →+* k) i,
      LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m ↔ ((Q i).map β).rank = D.m := by
    intro k _ β i
    obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM k β
    rw [GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords W G (𝓞 D.F) (act.toF D) n k β T (fun c => (A c).map β) hinj hrange hadd hscale
      (fun c x => heq _ (act.hom _) x)]
    have hsub : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((A c).map β) - (β.comp (t i)) c • LinearMap.id) :
        Submodule k (Fin n → k)) = LinearMap.range ((Q i).map β).mulVecLin := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range, RingHom.comp_apply]
      constructor
      · intro h
        exact ⟨y, hQ4 k β i y h⟩
      · rintro ⟨z, rfl⟩ c
        exact heig k β i c z
    rw [hsub]
    rfl
  refine ⟨fun R' _ β v hv => ?_, fun k _ _ β i => ?_⟩
  · obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM R' β
    obtain ⟨x, rfl⟩ := (hrange v).1 hv.1
    have hx := (tanT R' β T hinj hscale heq hrange D.ω (β ρ) x).1 hv
    refine ⟨fun i => T (((Q i).map β).mulVec x), fun i c =>
      (tanT R' β T hinj hscale heq hrange c _ _).2 (heig R' β i c x), ?_⟩
    rw [prod_ofFn_eq T (hT0 T hadd) hadd, ← hQ3 R' β x hx]
  · obtain ⟨r, hr⟩ := _root_.GlobalTheory.IdemRankLocal.rank_map_const W n (Q i) (hQ1 i)
    refine (rk k β i).2 ?_
    rw [hr, ← hr (AlgebraicClosure L) ((algebraMap L (AlgebraicClosure L)).comp (algebraMap W L))]
    exact (rk _ _ i).1 (hrank (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L)) i)

end GlobalTheory.LieExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.RealCoord

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def perL (X : Data E r) (x : Frame X.Ψ r) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ × Fin r → ℂ) where
  toFun := perC X x
  map_add' u v := by
    funext p
    simp only [perC, Pi.add_apply]
    split_ifs
    · simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    · rw [Matrix.mulVec_add, Pi.add_apply]
  map_smul' c u := by
    funext p
    simp only [perC, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [Matrix.mulVec_smul, Pi.smul_apply]

theorem hermC_col_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (a : Fin r)
    (c : Fin r → ℂ) : hermC τ G (FD.col x a) (x *ᵥ c) = ∑ b, FD.gram τ G x a b * conj (c b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, FD.gram, FD.col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem perL_injective (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Function.Injective (perL X x) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  funext τ
  have hd : (mat x τ).det ≠ 0 := (hx τ).1
  have hA : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have e : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos x τ).det := rfl
    rw [e, h0] at h
    simp at h
  set c : Fin r → ℂ := (mat x τ)⁻¹ *ᵥ u τ with hc
  have hu' : u τ = mat x τ *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mulVec]
  have h2 : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → c a = 0 := fun a ha => by
    have := congrFun hu (τ, a)
    change perC X x u (τ, a) = 0 at this
    simpa only [perC, if_neg ha] using this
  have h1 : X.gramPos x τ *ᵥ (fun b => conj (c (Fin.castLE X.p0_le b))) = 0 := by
    funext a
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := a.2
    have := congrFun hu (τ, Fin.castLE X.p0_le a)
    change perC X x u (τ, Fin.castLE X.p0_le a) = 0 at this
    simp only [perC, if_pos ha] at this
    rw [hu', hermC_col_mulVec] at this
    rw [Pi.zero_apply, ← this]
    simp only [Matrix.mulVec, dotProduct, Data.gramPos, Matrix.submatrix_apply]
    refine Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective _) _ _ (fun b hb => ?_) fun _ => rfl
    rw [h2 b fun h => hb ⟨⟨b, h⟩, rfl⟩, map_zero, mul_zero]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hA h1
  have h4 : c = 0 := by
    funext a
    by_cases ha : (a : ℕ) < X.p0
    · have := congrFun h3 ⟨a, ha⟩
      simpa using this
    · exact h2 a ha
  rw [hu', h4, Matrix.mulVec_zero]
  rfl

theorem perL_bijective (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Function.Bijective (perL X x) := by
  refine ⟨perL_injective X hx, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (perL_injective X hx)
  simp [Module.finrank_pi_fintype, mul_assoc]

end Lin

variable {D : D7}

theorem realM_tauE (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dite_eq_left h, ← GlobalTheory.PointAtPlace.tauE_injective h.choose_spec]

theorem realM_add (θ : InfFam D) {m n : ℕ} (v w : Mx D m n) (τ : D.host.E →+* ℂ) :
    realM θ (v + w) τ = realM θ v τ + realM θ w τ := by
  unfold realM
  split_ifs with h
  · funext i j
    show θ _ (infPart D (v i j + w i j)) = θ _ (infPart D (v i j)) + θ _ (infPart D (w i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]
  · rw [add_zero]

theorem continuous_realM {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.host.E →+* ℂ) (i : Fin m) (j : Fin n) :
    Continuous fun w : Mx D m n => realM θ w τ i j := by
  unfold realM
  split_ifs with h
  · exact (GlobalTheory.FockCompare.continuous_comp hθ _).comp ((continuous_apply j).comp (continuous_apply i))
  · exact continuous_const

theorem realM_lineAt {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (ρ : D.what₂.Tau) (u : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) (τ : D.host.E →+* ℂ) : realM θ (lineAt θ ρ u t) τ = t • realM θ (lineAt θ ρ u 1) τ := by
  have hL : IsLineAt θ ρ u (lineAt θ ρ u) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n ρ u)
  unfold realM
  split_ifs with h
  · rw [hL.2.2, hL.2.2]
    split_ifs
    · funext i j
      simp
    · rw [smul_zero]
  · rw [smul_zero]

theorem zOf_coordinates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), (∀ (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (v : WO V W), v.map (infPart D) = (ratW W V γ).map (infPart D) → zOf θ V W hr X idx x v = fun b => pv X idx x (colsR hr γ b)) ∧ (∀ v w : WO V W, zOf θ V W hr X idx x (v + w) = zOf θ V W hr X idx x v + zOf θ V W hr X idx x w) ∧ (∀ (τ : D.what₂.Tau) (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) (t : ℝ), zOf θ V W hr X idx x (lineAt θ τ u t) = (t : ℂ) • zOf θ V W hr X idx x (lineAt θ τ u 1)) ∧ Continuous (zOf θ V W hr X idx x ) ∧ (x ∈ X.dom → ∃ p : (Fin V.rank → Fin g → ℂ) →+ WO V W, Continuous p ∧ (∀ z, (p z).map (finPart D) = 0 ∧ zOf θ V W hr X idx x (p z) = z) ∧ ∀ w : WO V W, w.map (finPart D) = 0 → p (zOf θ V W hr X idx x w) = w) := by
  intro D ψ θ V W r g hr X bas idx _ hθ _ _ hM _ x
  have hz : ∀ w b j, zOf θ V W hr X idx x w b j =
      perL X x (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) (idx j) := fun _ _ _ => rfl
  refine ⟨fun γ v hv => ?_, fun v w => ?_, fun ρ u t => ?_, ?_, fun hx => ?_⟩
  · funext b j
    show perC X x _ (idx j) = per X x _ (idx j)
    rw [← perC_emb]
    congr 1
    funext τ a
    obtain ⟨ρ, hρ⟩ := (hM.psi τ.1).1 τ.2
    have e : infPart D (v (Fin.cast hr.symm a) b) = infPart D (incA D (γ (Fin.cast hr.symm a) b)) :=
      congrFun (congrFun hv _) _
    show realM θ v τ.1 _ _ = τ.1 (γ (Fin.cast hr.symm a) b)
    rw [hρ, realM_tauE, ← GlobalTheory.FockCompare.comp_incA hθ, ← e]
    rfl
  · funext b j
    rw [Pi.add_apply, Pi.add_apply, hz, hz, hz, ← Pi.add_apply (perL X x _), ← map_add (f := _)]
    refine congrFun (congrArg (perL X x) ?_) _
    funext τ a
    rw [realM_add]
    rfl
  · funext b j
    rw [Pi.smul_apply, Pi.smul_apply, hz, hz, Complex.coe_smul, ← Pi.smul_apply t (perL X x _), ← map_smul]
    refine congrFun (congrArg (perL X x) ?_) _
    funext τ a
    rw [realM_lineAt hθ]
    rfl
  · refine continuous_pi fun b => continuous_pi fun j => ?_
    simp only [hz]
    exact (continuous_apply (idx j)).comp ((perL X x).continuous_of_finiteDimensional.comp
      (continuous_pi fun τ => continuous_pi fun a => continuous_realM hθ τ.1 _ b))
  · obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L := LinearEquiv.ofBijective (perL X x) (perL_bijective X hx)
    have hL : ∀ u, L u = perL X x u := fun _ => rfl
    let pl : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩
    let p : (Fin V.rank → Fin g → ℂ) →+ WO V W :=
      { toFun := fun z => Matrix.of fun i b => σ fun ρ => L.symm (fun q => z b (idx.symm q)) (pl ρ) (Fin.cast hr i)
        map_zero' := by
          funext i b
          have : (fun q => (0 : Fin V.rank → Fin g → ℂ) b (idx.symm q)) = 0 := rfl
          rw [Matrix.of_apply, this, map_zero]
          exact σ.map_zero
        map_add' := fun z z' => by
          funext i b
          have : (fun q => (z + z') b (idx.symm q)) = (fun q => z b (idx.symm q)) + fun q => z' b (idx.symm q) := rfl
          rw [Matrix.of_apply, this, map_add (f := _)]
          exact σ.map_add _ _ }
    have hp : ∀ z i b, p z i b = σ fun ρ => L.symm (fun q => z b (idx.symm q)) (pl ρ) (Fin.cast hr i) :=
      fun _ _ _ => rfl
    refine ⟨p, ?_, fun z => ⟨?_, ?_⟩, fun w hw => ?_⟩
    · refine continuous_pi fun i => continuous_pi fun b => hσ.cont.comp (continuous_pi fun ρ => ?_)
      exact (continuous_apply (Fin.cast hr i)).comp ((continuous_apply (pl ρ)).comp
        (L.symm.toLinearMap.continuous_of_finiteDimensional.comp
          (continuous_pi fun q => (continuous_apply (idx.symm q)).comp (continuous_apply b))))
    · funext i b
      exact hσ.fin _
    · funext b j
      have e : (fun (τ : X.Ψ) a => realM θ (p z) τ.1 (Fin.cast hr.symm a) b) =
          L.symm (fun q => z b (idx.symm q)) := by
        funext τ a
        obtain ⟨ρ, hρ⟩ := (hM.psi τ.1).1 τ.2
        obtain rfl : τ = pl ρ := Subtype.ext hρ
        show realM θ (p z) (tauE D ρ) _ _ = _
        rw [realM_tauE]
        exact hσ.comp _ ρ
      rw [hz, e, ← hL, LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]
    · funext i b
      have e : (fun q => zOf θ V W hr X idx x w b (idx.symm q)) =
          L (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) := by
        funext q
        rw [hz, Equiv.apply_symm_apply, hL]
      rw [hp, e, LinearEquiv.symm_apply_apply]
      refine sub_eq_zero.1 (hσ.ext _ ?_ fun ρ => ?_)
      · have e1 : finPart D (w i b) = 0 := congrFun (congrFun hw i) b
        rw [RingHom.map_sub, hσ.fin, e1, sub_zero]
      · rw [RingHom.map_sub, RingHom.map_sub, hσ.comp, sub_eq_zero]
        show realM θ w (tauE D ρ) i b = _
        rw [realM_tauE]
        rfl

end GlobalTheory.AdTh.RealCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestTer
section
open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.UpperBoundDescent

theorem desc : ∀ (p : ℕ) [Fact p.Prime] (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ¬ IsUnit (p : T.V) → ∀ (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ) (FT : Fin dd → PS T.V 2 dd) (actT : OE → Fin dd → PS T.V 1 dd), UpFBr.UpFLaw p T'.V OE dd (fun i => MvPowerSeries.map φ (FT i)) (fun a i => MvPowerSeries.map φ (actT a i)) → UpFBr.UpFLaw p T.V OE dd FT actT := by
  intro p _ T T' φ hφ hfin hp OE _ _ dd FT actT h C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hb hf r W hW j
  have hinj : Function.Injective ((algebraMap O C).comp iota) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hp0 : (p : T.V) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    obtain ⟨m, u', hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
    have h1 : ((algebraMap O C).comp iota) ϖ = 0 := by
      rw [map_mul, map_pow, mul_eq_zero] at ha
      rcases ha with ha | ha
      · exact absurd ha (u.isUnit.map _).ne_zero
      · exact pow_eq_zero_iff'.1 ha |>.1
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp (by rw [hm]; simp)
    have h2 := congrArg ((algebraMap O C).comp iota) hm
    rw [map_natCast, map_mul, map_pow, h1, zero_pow hm0, mul_zero] at h2
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h2)
  obtain ⟨ι', hl, hc⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ hφ hfin.to_isIntegral iota hinj
  have key : ∀ {σ : Type} (f : MvPowerSeries σ T.V),
      MvPowerSeries.map ι' (MvPowerSeries.map φ f) = MvPowerSeries.map iota f := by
    intro σ f
    ext n
    simp only [MvPowerSeries.coeff_map, ← hc, RingHom.comp_apply]
  have := h C v O hv ι' hl w t hb hf r W (by simpa only [key] using hW) j
  simpa only [key] using this

end GlobalTheory.UpperBoundDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilInner

theorem integral_mul_conj_self {G : Type} [MeasurableSpace G] (ν : Measure G) {f : G → ℂ} (hf : Measurable f) :
    ∫ w, f w * conj (f w) ∂ν = ((∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν).toReal : ℂ) := by
  have e : ∀ w, f w * conj (f w) = ((‖f w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  congr 2
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integrable_mul_conj {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν] {f g : G → ℂ}
    (hf : Measurable f) (hg : Measurable g) (bf : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (bg : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C) :
    Integrable (fun w => f w * conj (g w)) ν := by
  obtain ⟨C, hC⟩ := bf
  obtain ⟨C', hC'⟩ := bg
  refine Integrable.of_bound (hf.mul (Complex.continuous_conj.measurable.comp hg)).aestronglyMeasurable (C * C')
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC w) (hC' w) (norm_nonneg _) ((norm_nonneg _).trans (hC w))

theorem inner_eq_of_meanSquare {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν]
    (P : (G → ℂ) → Prop) (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (c : ℂ) f, P f → P (c • f))
    (hm : ∀ f, P f → Measurable f) (hb : ∀ f, P f → ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C)
    (A : Module.End ℂ (G → ℂ)) (hA : ∀ f, P f → P (A f))
    (hu : ∀ f, P f → ∫⁻ w, ‖A f w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν) {f g : G → ℂ} (hf : P f) (hg : P g) :
    ∫ w, A f w * conj (A g w) ∂ν = ∫ w, f w * conj (g w) ∂ν := by
  have hI : ∀ f g, P f → P g → Integrable (fun w => f w * conj (g w)) ν := fun f g hf hg =>
    integrable_mul_conj ν (hm f hf) (hm g hg) (hb f hf) (hb g hg)
  have hN : ∀ f, P f → ∫ w, A f w * conj (A f w) ∂ν = ∫ w, f w * conj (f w) ∂ν := fun f hf => by
    rw [integral_mul_conj_self ν (hm _ (hA f hf)), integral_mul_conj_self ν (hm f hf), hu f hf]
  have ex : ∀ (c : ℂ) f g, P f → P g → ∫ w, (f + c • g) w * conj ((f + c • g) w) ∂ν =
      ∫ w, f w * conj (f w) ∂ν + conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν +
        c * conj c * ∫ w, g w * conj (g w) ∂ν := by
    intro c f g hf hg
    have i1 := hI f f hf hf
    have i2 := (hI f g hf hg).const_mul (conj c)
    have i3 := (hI g f hg hf).const_mul c
    have i4 := (hI g g hg hg).const_mul (c * conj c)
    have i12 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w))) ν := i1.add i2
    have i13 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w)) + c * (g w * conj (f w))) ν :=
      i12.add i3
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2,
      ← integral_add i12 i3, ← integral_add i13 i4]
    congr 1
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  have key : ∀ c : ℂ, conj c * ∫ w, A f w * conj (A g w) ∂ν + c * ∫ w, A g w * conj (A f w) ∂ν =
      conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν := by
    intro c
    have h := hN _ (hadd f _ hf (hsmul c g hg))
    rw [map_add (f := _), map_smul, ex c _ _ (hA f hf) (hA g hg), ex c f g hf hg, hN f hf, hN g hg] at h
    linear_combination h
  have h1 := key 1
  have h2 := key I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (I / 2) * h2 + (1 / 2 : ℂ) *
    (∫ w, A f w * conj (A g w) ∂ν - ∫ w, A g w * conj (A f w) ∂ν - ∫ w, f w * conj (g w) ∂ν +
      ∫ w, g w * conj (f w) ∂ν) * Complex.I_mul_I

theorem om_inner : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ p f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → ∫ w in 𝓕, om p f w * conj (om p f' w) ∂μ = ∫ w in 𝓕, f w * conj (f' w) ∂μ := by
  intro D ψ V W χV χW om hom μ 𝓕 hc p f f' hf hf'
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩
  exact inner_eq_of_meanSquare (μ.restrict 𝓕) (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) (fun _ h => h.cont.measurable)
    (fun _ h => GlobalTheory.OrientedHeis.theta_bounded hom.std h) (om p) (hom.om_pres p)
    (hom.om_unit μ 𝓕 hc.1 hc.2.1 p) hf hf'

end GlobalTheory.WeilInner
end

