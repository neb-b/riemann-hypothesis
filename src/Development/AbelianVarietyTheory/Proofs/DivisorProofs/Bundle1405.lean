module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsOfPulledBackLineBundlesOnFrames
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

namespace GlobalTheory.FlagPlucker

theorem det_mul_eq_sum_fun {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
  _root_.GlobalTheory.DeterminantProductExpansion.main A B

theorem exists_sum_minors_eq_one {R : Type} [CommRing R] {n k d : ℕ} (hd : d ≤ k) (A : Matrix (Fin n) (Fin k) R)
    (B : Matrix (Fin k) (Fin n) R) (hBA : B * A = 1) :
    ∃ c : (Fin d → Fin n) → R, ∑ r, c r * (A.submatrix r (Fin.castLE hd)).det = 1 := by
  have e : B.submatrix (Fin.castLE hd) id * A.submatrix id (Fin.castLE hd) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hBA,
      Matrix.submatrix_one _ (Fin.castLE_injective _)]
  refine ⟨fun r => ∏ a, B (Fin.castLE hd a) (r a), ?_⟩
  have := congrArg Matrix.det e
  rw [det_mul_eq_sum_fun, Matrix.det_one] at this
  exact this

end GlobalTheory.FlagPlucker

noncomputable section
namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem exists_mul_plkU_eq_one (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) :
    ∃ B : Matrix (Fin (Dw.mult σ)) (Fin Mc.n) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U), B * plkU F Mc k σ = 1 := by
  obtain ⟨w, hw⟩ := F.split k σ
  have hm : ∀ (M M' : MChart Y) (hle : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ (M.U ⊓ M'.U)) (S : Type) [CommRing S]
      (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)),
      ((chg M M').map (π.appLE _ _ hle).hom).map (ev z _ hz) =
        (chg M M').map (ev (z ≫ π) _ (le_preimage_map π hle hz)) := by
    intro M M' hle S _ z hz
    rw [Matrix.map_map]
    ext a b
    exact ev_appLE z π hle hz _ _
  have hle1 : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ ((F.M k).U ⊓ Mc.U) := fun _ hp => ⟨F.le k hp.1, hp.2⟩
  have hle2 : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ (Mc.U ⊓ (F.M k).U) := fun _ hp => ⟨hp.2, F.le k hp.1⟩
  have hC : (chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom *
      (chg Mc (F.M k).toMChart).map (π.appLE _ _ hle2).hom = 1 := by
    ext i j
    refine ext_ev fun S _ z hz => ?_
    have e : (((chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom *
        (chg Mc (F.M k).toMChart).map (π.appLE _ _ hle2).hom)).map (ev z _ hz) =
        (1 : Matrix (Fin (F.M k).n) (Fin (F.M k).n) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U)).map (ev z _ hz) := by
      have hx := le_preimage_map π hle1 hz
      have hx' := le_preimage_map π hle2 hz
      rw [Matrix.map_mul, hm _ _ hle1, hm _ _ hle2,
        chg_map _ _ (z ≫ π) (le_preimage_mono inf_le_left hx) (le_preimage_mono inf_le_right hx),
        chg_map _ _ (z ≫ π) (le_preimage_mono inf_le_left hx') (le_preimage_mono inf_le_right hx'),
        Module.Basis.toMatrix_mul_toMatrix,
        Module.Basis.toMatrix_self, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrFun (congrFun e i) j
  refine ⟨(w.map (resG Z (inf_le_left : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ F.U k))) *
    (chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom, ?_⟩
  unfold plkU
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((chg (F.M k).toMChart Mc).map _), hC, Matrix.one_mul,
    ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_mem_basicOpen_plkMinor (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ)
    (m : Fin (Dw.mult σ)) (z : Z) (hz : z ∈ F.U k ⊓ π ⁻¹ᵁ Mc.U) :
    ∃ r, z ∈ Z.basicOpen (plkMinor F Mc k σ m r) := by
  obtain ⟨B, hB⟩ := exists_mul_plkU_eq_one F Mc k σ
  obtain ⟨cf, hc⟩ := exists_sum_minors_eq_one (d := (m : ℕ) + 1) m.2 _ B hB
  by_contra hno
  push_neg at hno
  have hmax : (Z.presheaf.germ _ z hz).hom (∑ r, cf r * plkMinor F Mc k σ m r) ∈
      IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Ideal.sum_mem _ fun r _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => hno r ?_)
    exact (Scheme.mem_basicOpen Z _ z hz).2 hu
  have h1 : ∑ r, cf r * plkMinor F Mc k σ m r = 1 := hc
  rw [h1, map_one] at hmax
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hmax)

end GlobalTheory.FlagPlucker
end

noncomputable section
namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj

theorem iSup_nonzeroLocus_plk : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ q, (t q).f = plkLoc F Mc g hg σ m q) → ⨆ q, nonzeroLocus (t q) = ⊤ := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F Mc T g hg σ m t ht
  refine eq_top_iff.2 fun p _ => ?_
  obtain ⟨k, hk⟩ : ∃ k, g.base p ∈ F.U k := by
    have : g.base p ∈ (⨆ k, F.U k) := by rw [F.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hpM : g.base p ∈ π ⁻¹ᵁ Mc.U := by
    have := hg (show p ∈ (⊤ : T.Opens) from trivial)
    simpa using this
  obtain ⟨r, hr⟩ := exists_mem_basicOpen_plkMinor F Mc k σ m (g.base p) ⟨hk, hpM⟩
  let j : ((F.LL (ind σ m)).pull g).ι := fun _ => k
  have hpj : p ∈ ((F.LL (ind σ m)).pull g).U j := mem_pull.2 hk
  let q : Fin (plkNum Mc m + 1) := Fin.succ (Fintype.equivFin _ r)
  have hq : plkIdx Mc m q = some r := by simp [q, plkIdx]
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨q, (mem_nonzeroLocus_iff_basicOpen (t q) hpj).2 ?_⟩
  rw [congrFun (ht q) j]
  unfold plkLoc
  split
  · rename_i h; rw [hq] at h; exact absurd h (by simp)
  · rename_i r' h
    rw [hq] at h
    cases h
    rw [Scheme.basicOpen_appLE]
    exact ⟨hpj, hr⟩

end GlobalTheory.FlagPlucker
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharArchimedeanEqExpNondegenerate
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.StdBeta

theorem at_arch (F : Type) [Field F] [NumberField F] (a : mixedEmbedding.mixedSpace F) :
    At (M := AF F) (evI F) (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · exact mul_zero u.2

theorem evI_arch (F : Type) [Field F] [NumberField F] (a : mixedEmbedding.mixedSpace F) :
    evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) = a :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

theorem stdBeta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧ ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 := by
  intro F _ _ ψ hψ
  refine ⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun a => ?_, fun a ha => ?_⟩
  · rw [hψ.2.2 _ (at_arch F a), evI_arch]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg]
    ring_nf
  · by_contra h
    push_neg at h
    exact ha (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace a fun b => by
      have := h b
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      exact this)

end GlobalTheory.StdBeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharArchimedeanExpRealLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdCharLin

theorem continuous_ofMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem stdChar_mixed_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsStdChar D ψ (-1) → IsInfFam θ →
    ∃ β : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧
      ∀ a, β a = -(∑ ρ, θ ρ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a) ⊗ₜ[D.host.F]
        (1 : D.host.E))).re := by
  intro D ψ θ hψ hθ
  obtain ⟨hc, hall⟩ := hψ
  have key := hall.2 θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F with he
  let z : Ainf D.host.F → ℂ := fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))
  have hkey : ∀ x, ψ ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x) := fun x => key x
  have him : ∀ x, (z x).im = 0 := by
    intro x
    have h1 := hc.2.1 ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F)
    rw [hkey x, Complex.norm_exp] at h1
    have hre : (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x).re = 2 * Real.pi * (z x).im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_eq_one_iff] at h1
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    rcases mul_eq_zero.1 h1 with h | h
    · linarith
    · exact h
  have hzadd : ∀ x y, z (x + y) = z x + z y := by
    intro x y
    simp only [z, TensorProduct.add_tmul, map_add (f := _), Finset.sum_add_distrib]
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℝ :=
    { toFun := fun a => -(z (e.symm a)).re
      map_zero' := by simp [z]
      map_add' := by intro a b; simp only [map_add (f := _), hzadd, Complex.add_re, neg_add] }
  have hg : Continuous g := by
    have : Continuous fun x : Ainf D.host.F => z x :=
      continuous_finsetSum _ fun ρ _ => (hθ ρ).2
    exact (Complex.continuous_re.comp (this.comp (continuous_ofMixed D.host.F))).neg
  refine ⟨(g.toRealLinearMap hg : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ), ?_, fun a => rfl⟩
  intro a
  have hz : z (e.symm a) = ((z (e.symm a)).re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hkey (e.symm a)]
  congr 1
  change _ = 2 * Real.pi * Complex.I * ((-(z (e.symm a)).re : ℝ) : ℂ)
  rw [hz]
  push_cast
  simp only [Complex.ofReal_re]
  ring

end GlobalTheory.StdCharLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeFlagUnipotentRadical
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix

namespace GlobalTheory.StdPar

theorem unip_le_unipFlag_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S m hm hS g hg
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, h⟩ => h.trans (hS k hk), fun h => ⟨m, hm, h⟩⟩
  apply Subgroup.subset_closure
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have key : ∀ y ∈ colSpan F X {l | ∃ k ∈ S, l ≤ k ∧ k < i.castLE m.2},
        ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j : Fin (m.val + 1), (S.filter fun k => k.val < i.val).card ≤
          (S.filter fun k => k.val < j.val).card → a j = 0) ∧ y = adMat F (initCols X m) *ᵥ a := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, ⟨k, hk, hlk, hki⟩, rfl⟩ := hy
        have hl : l.val < m.val + 1 := Nat.lt_succ_of_le (hlk.trans (hS k hk))
        refine ⟨Pi.single ⟨l.val, hl⟩ 1, fun j hj => ?_, ?_⟩
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          refine absurd hj (not_le.2 (Finset.card_lt_card ⟨fun t ht => ?_, fun h => ?_⟩))
          · rw [Finset.mem_filter] at ht ⊢
            exact ⟨ht.1, lt_trans (lt_of_lt_of_le ht.2 hlk) hki⟩
          · have := (Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨hk, hki⟩))).2
            exact absurd this (not_lt.2 hlk)
        · rw [mulVec_single_one]
          rfl
      | zero => exact ⟨0, fun _ _ => rfl, (mulVec_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨b, hb, rfl⟩ := hz
        exact ⟨a + b, fun j hj => by rw [Pi.add_apply, ha j hj, hb j hj, add_zero], (mulVec_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        exact ⟨c • a, fun j hj => by rw [Pi.smul_apply, ha j hj, smul_zero], (mulVec_smul _ _ _).symm⟩
    have := (Subgroup.mem_iInf.1 hg.1 (i.castLE m.2)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := key _ this
    refine ⟨a, ha, ?_⟩
    rw [sub_mulVec, one_mulVec]
    exact e
  · have := hg.2.2 (fun i => inclR (F := F) (AF F) (x i)) (by
      rw [e1, mem_colPerp_iff]
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    rw [e1, mem_colSpan_iff] at this
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

end GlobalTheory.StdPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeIsotropicFlagStabili
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
namespace GlobalTheory.StdParFlag

open Matrix

theorem unip_le_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T m _ _ _
  classical
  have key : ∀ p ∈ GlobalTheory.StdPar.unip σ J X S, ∃ B : Matrix (Fin (m.val + 1)) (Fin (m.val + 1)) (AF F ⊗[F] E),
      B.BlockTriangular (fun i => (T.filter fun k => k.val < i.val).card) ∧
      (matHom _ σ J p).1 * adMat F (GlobalTheory.StdPar.initCols X m) = adMat F (GlobalTheory.StdPar.initCols X m) * B := by
    intro p hp
    have span_lemma : ∀ (i : Fin (m.val + 1)) (I : Set (Fin r)), (∀ l ∈ I, l.val < i.val) →
        ∀ y ∈ GlobalTheory.StdPar.colSpan F X I, ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j, i.val ≤ j.val → a j = 0) ∧
          adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a = y := by
      intro i I hI y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hx
        have hl' : l.val < m.val + 1 := by have := hI l hl; have := i.2; omega
        refine ⟨Pi.single ⟨l.val, hl'⟩ 1, fun j hj => Pi.single_eq_of_ne (fun e => ?_) _, ?_⟩
        · have := hI l hl; rw [e] at hj; simp at hj; omega
        · rw [mulVec_single_one]; rfl
      | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], by rw [mulVec_add]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨c • a, fun j hj => by simp [ha j hj], by rw [mulVec_smul]⟩
    have hcol : ∀ i : Fin (m.val + 1), ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j, (fun k : Fin (m.val + 1) => k.val) i ≤ (fun k : Fin (m.val + 1) => k.val) j → a j = 0) ∧
        ((matHom _ σ J p).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (GlobalTheory.StdPar.initCols X m k i)) =
          adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a := by
      intro i
      have h := (Subgroup.mem_iInf.1 hp.1 (Fin.castLE m.2 i)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
      have hv : (fun k => inclR (F := F) (AF F) (GlobalTheory.StdPar.initCols X m k i)) = (adMat F X)ᵀ (Fin.castLE m.2 i) := rfl
      rw [hv, sub_mulVec, one_mulVec]
      obtain ⟨a, ha, e⟩ := span_lemma i _ (fun l hl => by
        obtain ⟨k, _, hlk, hki⟩ := hl
        have := Fin.lt_def.1 (lt_of_le_of_lt hlk hki)
        simpa using this) _ h
      exact ⟨a, ha, e.symm⟩
    obtain ⟨A, hA, e⟩ := lower_iff.1 hcol
    refine ⟨1 + A, fun l j hlt => ?_, ?_⟩
    · have hjl : j.val ≤ l.val := by
        by_contra hc
        refine absurd hlt (not_lt.2 (Finset.card_le_card fun k hk => ?_))
        simp only [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, by omega⟩
      have hne : l ≠ j := fun h => by subst h; exact lt_irrefl _ hlt
      rw [Matrix.add_apply, Matrix.one_apply_ne hne, hA l j hjl, add_zero]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  intro p hp
  exact ⟨key p hp, key p⁻¹ (inv_mem hp)⟩

end GlobalTheory.StdParFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdPar

section DimensionMonotonicity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}

theorem unip_maps_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  have key : colSpan F X I ≤ (colSpan F X I).comap (matHom _ σ J g).1.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (Subgroup.mem_iInf.1 hg.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
    have h2 : colSpan F X {l | ∃ k ∈ T, l ≤ k ∧ k < i} ≤ colSpan F X I := by
      refine Submodule.span_mono (Set.image_mono ?_)
      rintro l ⟨k, -, hlk, hki⟩
      exact hI i hi l (lt_of_le_of_lt hlk hki)
    have h3 : (fun i => (adMat F X)ᵀ i) i ∈ colSpan F X I := Submodule.subset_span ⟨i, hi, rfl⟩
    show (matHom _ σ J g).1 *ᵥ _ ∈ colSpan F X I
    have := add_mem (h2 h1) h3
    rwa [sub_add_cancel] at this
  exact key hy

theorem unip_iff_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) (y : Fin n → AF F ⊗[F] E) :
    y ∈ colSpan F X I ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  refine ⟨unip_maps_colSpan hg hI, fun h => ?_⟩
  have := unip_maps_colSpan (inv_mem hg) hI h
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

end DimensionMonotonicity

theorem unip_mono_of_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T hTS g hg
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩,
    ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩⟩
  · rintro i ⟨k, hk, hik, hkj⟩ l hl
    exact ⟨k, hk, (le_of_lt (lt_of_lt_of_le hl hik)), hkj⟩
  · refine Submodule.span_mono (Set.image_mono ?_) ((Subgroup.mem_iInf.1 hg.1 j).2 y hy)
    rintro l ⟨k, hk, h1, h2⟩
    exact ⟨k, hTS hk, h1, h2⟩
  · rintro i ⟨k, hk, hik⟩ l hl
    exact ⟨k, hk, le_of_lt (lt_of_lt_of_le hl hik)⟩
  · have hy' : y ∈ colPerp σ J X {i | ∃ k ∈ T, i ≤ k} := by
      simp only [colPerp, Submodule.mem_iInf] at hy ⊢
      rintro i ⟨k, hk, hik⟩
      exact hy i ⟨k, hTS hk, hik⟩
    refine Submodule.span_mono (Set.image_mono ?_) (hg.2.2 y hy')
    rintro l ⟨k, hk, h1⟩
    exact ⟨k, hTS hk, h1⟩

end GlobalTheory.StdPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlaneStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_restricted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E)
    (ι : Matrix (Fin d) (Fin d₁) E), ιᵀ * JW * ι.map σ = JW₁ → ∀ z z' : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (1 : Matrix (Fin n) (Fin n) E) * z * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)ᵀ)
        ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (1 : Matrix (Fin n) (Fin n) E) * z' * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)ᵀ) = symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW₁) z z' := by
  first | exact @GlobalTheory.MixedLagrGram.symp_restrict_gram | exact GlobalTheory.MixedLagrGram.symp_restrict_gram | (intros; apply GlobalTheory.MixedLagrGram.symp_restrict_gram <;> assumption)
end

