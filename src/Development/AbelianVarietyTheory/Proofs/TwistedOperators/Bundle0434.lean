module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfWaves

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

theorem isSBHalf_trans {a : AE D} {Λ : AddSubgroup (WO S T)} {x : WO S T} (hx : IsHalf a x) {k : ℕ} (hk : 0 < k)
    (hkx : k • x ∈ Λ) : IsSBHalf a Λ fun t => halfInd a Λ (t + x) := by
  have hx' := (isHalf_iff S T).1 hx
  refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have h : t + x ∈ Λ ∧ IsHalf a (t + x) := by
      by_contra h
      exact ht (if_neg h)
    refine (isHalf_iff S T).2 ?_
    exact (add_mem_cancel_right hx').1 ((isHalf_iff S T).1 h.2)
  · have hm : k • u ∈ Λ ⊓ half S T a :=
      nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k
    rw [halfInd_eq_ind]
    change ind _ (t + k • u + x) = ind _ (t + x)
    rw [add_right_comm]
    exact ind_add _ _ hm
  · have h : t + x ∈ Λ ∧ IsHalf a (t + x) := by
      by_contra h
      exact ht (if_neg h)
    have e : k • t = k • (t + x) - k • x := by rw [nsmul_add, add_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem h.1 k) hkx

theorem isSBHalf_modul (ψ : AddChar (AF D.host.F) ℂ) {a : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T u y) = 1)
    {y : WO S T} (hy : IsHalf (cA D a) y) {k : ℕ} (hk : 0 < k) (hky : k • y ∈ Λ) {Φ : WO S T → ℂ}
    (hΦ : IsSBHalf a Λ Φ) : IsSBHalf a Λ fun t => ψ (symplO S T t y) * Φ t := by
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  obtain ⟨a1, k', hk1, a2, a3⟩ := hΦ
  refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_nsmul]
      exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
    have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
      rw [mul_nsmul']
      exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _
        ⟨hky, nsmul_mem ((isHalf_iff S T).1 hy) k⟩)
    simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
  · rw [mul_nsmul']
    exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k

end GlobalTheory.HalfWaves

namespace GlobalTheory.PlaceTensor

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.HalfWaves

theorem halfWaves_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → a * cA D a = 0 → infPart D a = 0 → (∀ x y : WO S T, IsHalf a x → IsHalf (cA D a) y → IsSBHalf a (latO S T ΛS ΛT fun _ => True) (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Tm (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) = heisO ψ S T y (heisO ψ S T x f₀)) ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → Φ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧ Ψ = fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)} := by
  intro D ψ S T ΛS ΛT hψ hS hT e he _ hinf
  have hSfull := GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS
  have hTfull := GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin0 := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin0 k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hsb : ∀ x, IsHalf e x → IsSBHalf e (latO S T ΛS ΛT fun _ => True)
      fun t => halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := fun x hx => by
    obtain ⟨k, hk, hk'⟩ := exists_nsmul_mem_latO' hSfull hTfull x (infPart_of_half hinf hx)
    exact isSBHalf_trans hx hk hk'
  have hmod : ∀ x y, IsHalf e x → IsHalf (cA D e) y → IsSBHalf e (latO S T ΛS ΛT fun _ => True)
      fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := fun x y hx hy => by
    obtain ⟨k, hk, hk'⟩ := exists_nsmul_mem_latO' hSfull hTfull y (infPart_of_half (infPart_cA hinf) hy)
    exact isSBHalf_modul ψ hLL' hy hk hk' (hsb x hx)
  refine ⟨fun x y hx hy => ⟨hmod x y hx hy, fun f₀ Tm hTm => ?_⟩, fun Φ hΦ => ?_⟩
  · have v := hTm.vac
    rw [one_smul] at v
    rw [hTm.modul _ (hsb x hx) y hy, hTm.trans _ (GlobalTheory.isSBHalf_halfInd e _) x hx, v]
  · have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
        ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
      obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
      exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
        (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
        fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
    refine (Submodule.span_le.2 ?_) hm
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        ψ (symplO S T x y) • fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := by
      funext t
      simp only [wave, Pi.smul_apply, smul_eq_mul, halfInd_eq_ind, symplO_add_left, AddChar.map_add_eq_mul]
      ring
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, y, (isHalf_iff S T).2 hx, (isHalf_iff S T).2 hy, rfl⟩)

end GlobalTheory.PlaceTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteKernelEqCharMulThetaKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

theorem isThetaFunO_small_of_isMatched {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hM : IsMatched B t ρ i j Θ Θ') :
    ∀ d ∈ Θ'.support, IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hM
  intro d hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, hd₁⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hP)
  obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hd₁)
  obtain ⟨hA, hB⟩ := hloc d₀ hd₀
  have hv₁ := (ρ.vT_is t i j i.2.le j.2).2.theta
  have hv₂ := (ρ.vX_is i j i.2 j.2.le).2.theta
  have hf₁ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hA.2 hv₁
  have hf₂ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hB.2 hv₂
  exact ⟨GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ P.1.2 hf₁,
    GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ P.2 hf₂⟩

theorem kerSmall_eq_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωB : GlobalTheory.Grid.WRep (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerSmall W Θ' g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωB u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumB W Θ') := by
  intro D T L sc G μ₀ hL W t i j ωB hωB B ρ Θ Θ' hM g g₁ u
  have hth := isThetaFunO_small_of_isMatched W B ρ t i j Θ Θ' hM
  have hω := (GlobalTheory.Grid.isWeil_false W.ψ _ _ _ _ ωB).mp hωB
  have key : ∀ d ∈ Θ'.support, W.kerA (.down t i j) d.1.2 g u * W.kerA (.right i j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
        ωB (u, GlobalTheory.SquareComm.blk _ _ (g, g₁))
          (box2 (S := G.V (.grid i j)) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j)) d.1.2
            (fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y))) 0 := by
    intro d hd
    have h := (GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωB hω d.1.2 d.2 (hth d hd).1 (hth d hd).2).2 g u g₁
    have hadj : GlobalTheory.SeesawSmall.adjFn (G.V (.grid i j)) (G.V (.grid (i + 1) j)) d.2 =
        fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y) := by
      funext y
      exact congrArg d.2 (GlobalTheory.AdjSwap.dagger_eq_adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y)
    rw [hadj] at h
    exact h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [kerSmall, GlobalTheory.SquareDict.datumB, thetaKO, Finsupp.sum, map_sum, Finset.sum_apply, map_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d hd]
  ring

end GlobalTheory.SquareDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceCoord

theorem isOpen_isCompact_of_comm {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K]
    {m n : ℕ} (O : AddSubgroup K) (ho : IsOpen (O : Set K)) (hc : IsCompact (O : Set K))
    (A : AddSubgroup (Matrix (Fin m) (Fin n) K)) {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    (h1 : ∀ y : Matrix (Fin m) (Fin n) K, (∀ i j, y i j ∈ O) → k • y ∈ A)
    (h2 : ∀ y ∈ A, ∀ i j, (M : K) * y i j ∈ O) :
    IsOpen (A : Set (Matrix (Fin m) (Fin n) K)) ∧ IsCompact (A : Set (Matrix (Fin m) (Fin n) K)) := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hM' : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hU : IsOpen {y : Matrix (Fin m) (Fin n) K | ∀ i j, (k : K)⁻¹ * y i j ∈ O} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ho.preimage (f := fun y : Matrix (Fin m) (Fin n) K => (k : K)⁻¹ * y i j) (by fun_prop)
  have hA : IsOpen (A : Set (Matrix (Fin m) (Fin n) K)) := by
    refine A.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds fun i j => by simp) fun y hy => ?_)
    have := h1 ((k : K)⁻¹ • y) hy
    rwa [← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hk', one_smul] at this
  refine ⟨hA, ?_⟩
  have hC : IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => (fun x => (M : K)⁻¹ * x) '' O) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc.image (by fun_prop)
  refine IsCompact.of_isClosed_subset (s := Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => (fun x => (M : K)⁻¹ * x) '' O) hC (A.isClosed_of_isOpen hA) fun y hy i _ j _ => ⟨_, h2 y hy i j, ?_⟩
  simp only [inv_mul_cancel_left₀ hM']

def mulHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ} (P : GL (Fin m) K)
    (Q : GL (Fin n) K) : Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin m) (Fin n) K where
  toFun x := P.val * x * Q.val
  invFun x := (P⁻¹).val * x * (Q⁻¹).val
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv x := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

variable {D : D7}

theorem toEAf_mem {w : AE D} (hw : finPart D w ∈ intAE D) : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

variable {v : FinPl D} {S T : HSp D} {e : AE D} {π : AE D →+* Fv D.host.F v}

theorem exists_half (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1)
    (y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) : ∃ t : WO S T, IsHalf e t ∧ t.map π = y := by
  choose s hs using hπ.1
  refine ⟨Matrix.of fun i j => e * s (y i j), fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · rw [Matrix.of_apply, ← mul_assoc, he]
  · rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_mul, h1, one_mul, hs]

theorem bijOn_map (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1) :
    Set.BijOn (fun t : WO S T => t.map π) {t | IsHalf e t} Set.univ := by
  refine ⟨Set.mapsTo_univ _ _, fun x hx y hy h => Matrix.ext fun i j => ?_, fun y _ => exists_half hπ he h1 y⟩
  have h0 : π (x i j - y i j) = 0 := by
    rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h i) j
  rw [hπ.2.1, mul_sub, hx i j, hy i j, sub_eq_zero] at h0
  exact h0

private theorem selfDual_full {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem isOpen_isCompact_map {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1)
    (hinf : infPart D e = 0) :
    IsOpen ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) ∧
    IsCompact ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) := by
  have : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F _).injective
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨k, hk, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) (selfDual_full S ΛS hS) (selfDual_full T ΛT hT)
  have hset : ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) =
      (((latO S T ΛS ΛT fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e).map π.toAddMonoidHom.mapMatrix :
        AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))) := by
    rw [AddSubgroup.coe_map]
    congr 1
    ext t
    exact and_congr_right fun _ => GlobalTheory.PlaceModel.isHalf_iff S T
  rw [hset]
  refine isOpen_isCompact_of_comm (v.adicCompletionIntegers D.host.F).toSubring.toAddSubgroup
    (Valued.isOpen_valuationSubring _) (isCompact_iff_compactSpace.2 (Formalism.L2.Col.rlt_compact_int v)) _ hk hM
    (fun y hy => ?_) ?_
  · obtain ⟨t, ht, rfl⟩ := exists_half hπ he h1 y
    refine ⟨k • t, ⟨hmul t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht) fun i j => toEAf_mem ?_,
      nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) k⟩, map_nsmul _ _ _⟩
    rw [← ht i j]
    exact (hπ.2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 (hy i j))
  · rintro _ ⟨t, ⟨ht, ht'⟩, rfl⟩ i j
    have h2 : toEAf D ((M : AE D) * t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [RingHom.map_mul, map_natCast]; exact hden t ht i j
    have h3 : finPart D (e * ((M : AE D) * t i j)) ∈ intAE D := by
      rw [mul_left_comm, (GlobalTheory.PlaceModel.isHalf_iff S T).2 ht' i j]
      exact GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h2
    have h4 := GlobalTheory.SplitHecke.isInt_Ov.1 ((hπ.2.2.2 _).1 h3)
    rw [RingHom.map_mul, map_natCast] at h4
    exact h4

theorem infPart_split (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨a1, a2, v, ε, ⟨β, rfl, -⟩, a3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have hi' : e * (e + cA D e) = e := by rw [mul_add, a1, a2, add_zero]
  rw [← hi', a3, RingHom.map_mul, h0, mul_zero]

theorem isCoord_mapCo : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord e (latO S T ΛS ΛT fun _ => True) (mapCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), mapCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ T BT h)⁻¹).val * mapCo φ S T BS BT t * (grpCo φ S BS g).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  have hπ := (_root_.GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hcomp : mapCo φ S T BS BT = mulHomeo BT⁻¹ BS ∘ fun t : WO S T => t.map (rdA φ) := rfl
  have hoc := isOpen_isCompact_map (S := S) (T := T) hS hT hπ he.1.1 he.2.2 (infPart_split he.1)
  refine ⟨⟨fun x y => ?_, ?_, ?_, ?_⟩, fun g h t => ?_⟩
  · unfold mapCo
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
  · rw [hcomp]
    exact (Set.bijOn_univ.2 (mulHomeo BT⁻¹ BS).bijective).comp (bijOn_map hπ he.1.1 he.2.2)
  · rw [hcomp, Set.image_comp]
    exact (mulHomeo BT⁻¹ BS).isOpenMap _ hoc.1
  · rw [hcomp, Set.image_comp]
    exact hoc.2.image (mulHomeo BT⁻¹ BS).continuous
  · have e1 : ((grpCo φ T BT h)⁻¹).val = (BT⁻¹).val * (mt T h⁻¹).map (rdA φ) * BT.val := by
      have : (grpCo φ T BT h)⁻¹ = grpCo φ T BT h⁻¹ := by
        unfold grpCo
        rw [map_inv, map_inv, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
      rw [this]; rfl
    have e2 : (grpCo φ S BS g).val = (BS⁻¹).val * (mt S g).map (rdA φ) * BS.val := rfl
    rw [e1, e2]
    unfold mapCo actO
    rw [inv_inv, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]

end GlobalTheory.PlaceCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockRealMove

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) {x : GA D V} (hx : x ∈ GfC V) :
    compAt θ τ (mt V x) = 1 :=
  GlobalTheory.LocWeil.CompactPart.infMat_of_fin V (θ τ) hx

theorem om_fin_fockVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x ∈ GfC S, ∀ y ∈ GfC T, IsThetaFunO ψ S T (om (x, y) f) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x, y) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sT f hf hvac x hx y hy
  refine ⟨hW.om_pres _ _ hf, fun τ z => ?_⟩
  have hS : sS τ * compAt θ τ (mt S x) = compAt θ τ (mt S x) * sS τ := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, Matrix.mul_one, Matrix.one_mul]
  have hT : sT τ * compAt θ τ (mt T y) = compAt θ τ (mt T y) * sT τ := by
    rw [compAt_mt_of_mem_GfC θ τ T hy, Matrix.mul_one, Matrix.one_mul]
  have key := GlobalTheory.FockMove.om_annih hW hθ x y τ hS hT (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) hf
  rw [hvac τ, map_zero] at key
  have e : compAt θ τ (mt T y) * (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) * compAt θ τ (mt S x⁻¹) = z := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, compAt_mt_of_mem_GfC θ τ S (inv_mem hx),
      compAt_mt_of_mem_GfC θ τ T hy, compAt_mt_of_mem_GfC θ τ T (inv_mem hy)]
    simp
  rw [e] at key
  exact key.symm

end GlobalTheory.FockRealMove

end
end

