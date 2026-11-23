module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.V4.TwoPass

theorem large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem ev_and {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem ev_mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

end GlobalTheory.Mem.Top.V4.TwoPass

namespace GlobalTheory.Mem.Top.V4

open TwoPass

end GlobalTheory.Mem.Top.V4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexStabilizerEqLocalRelIndex
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)

namespace GlobalTheory.LocRelIndex

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (J : Subgroup (GAf L n)) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ s.loc n κ ∈ H)) → J.relIndex (GlobalTheory.HeckeScalarSph.locK n s.v) = H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) := by
  intro L _ _ _ n s J H hJH
  set K := GlobalTheory.HeckeScalarSph.locK (L := L) n s.v with hK
  set O := Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO
  let φ : K →* O :=
    ((s.loc n).comp K.subtype).codRestrict O (fun κ => (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s κ.2.2).2 κ.2.1)
  have hsurj : Function.Surjective φ := by
    intro A
    obtain ⟨x, hx, -⟩ := (_root_.GlobalTheory.SplitAdelic.main L n s).2.2 A.1
    refine ⟨⟨x, ?_, hx.1⟩, ?_⟩
    · exact (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx.1).1 (hx.2 ▸ A.2)
    · exact Subtype.ext hx.2
  have hcomap : J.subgroupOf K = (H.subgroupOf O).comap φ := by
    ext κ
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact hJH κ κ.2.2
  rw [Subgroup.relIndex, Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj]

end GlobalTheory.LocRelIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowActSmulOfWeight
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.RowsSign

open MvPolynomial
open scoped ComplexOrder

section General

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem degree_of_colWeight {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem rowAct_smul_of_weight {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f ν) :
    Formalism.GradedWeylDivisibility.rowAct R (c • g) f = c ^ (∑ j, ν j) • Formalism.GradedWeylDivisibility.rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

def totDeg (lam : ι → DomWeight n) : ℕ := ∑ τ, ∑ j, (lam τ).natW j

theorem blockAct_smul_of_mem (lam : ι → DomWeight n) (a : K) (M : ι → Matrix (Fin n) (Fin n) K)
    {y : Formalism.L2.DIV.Pol K ι n} (hy : y ∈ Formalism.L2.DIV.VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => a • M τ) y = a ^ totDeg lam • Formalism.GradedWeylDivisibility.blockAct K M y := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have hT := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => a • M τ)).1
    have hT' := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (a • M τ) (F τ)) =
        C (a ^ (∑ j, (lam τ).natW j)) * Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (M τ) (F τ)) := by
      intro τ
      rw [rowAct_smul_of_weight a (M τ) (F τ) (Formalism.GradedWeylDivisibility.mem_dualWeyl_iff.1 (hF τ)).1, map_smul, smul_eq_C_mul]
    rw [map_prod, map_prod]
    simp only [hT, hT']
    rw [Finset.prod_congr rfl fun τ _ => h2 τ, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
      smul_eq_C_mul]
    rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]

variable [StarRing K]

def negSign (lam : ι → DomWeight n) : K := gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * (-1) ^ totDeg lam

theorem pairK_neg (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (x y : Formalism.L2.DIV.VV K lam) :
    pairK lam (fun τ => -G τ) x y = negSign lam * pairK lam G x y := by
  have hy := blockAct_smul_of_mem lam (-1 : K) (fun τ => (G τ)ᵀ) y.2
  have hT : (fun τ => (-G τ)ᵀ) = fun τ => (-1 : K) • (G τ)ᵀ := by
    funext τ
    rw [Matrix.transpose_neg, neg_one_smul]
  have hg : gramTw lam (fun τ => -G τ) = gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam G := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← mul_zpow, ← Matrix.det_mul, neg_mul, one_mul]
  simp only [pairK, pairP, LinearMap.domRestrict₁₂_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul]
  rw [hT, hy, map_smul, hg, negSign, smul_eq_mul]
  ring

theorem negSign_mul_self (lam : ι → DomWeight n) : negSign (K := K) lam * negSign lam = 1 := by
  have hd : ((-1 : Matrix (Fin n) (Fin n) K)).det * ((-1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [← Matrix.det_mul, neg_mul_neg, one_mul, Matrix.det_one]
  have hz : ∀ e : ℤ, ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e * ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e = 1 := by
    intro e
    rw [← mul_zpow, hd, _root_.one_zpow]
  have hp : ((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hgg : gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) = 1 := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => hz _
  calc negSign (K := K) lam * negSign lam
      = (gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K))) *
        (((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam) := by unfold negSign; ring
    _ = 1 := by rw [hgg, hp, one_mul]

end General

end GlobalTheory.RowsSign

namespace GlobalTheory.RowsSign

open scoped ComplexOrder InnerProductSpace

theorem pairV_neg_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (φ : K →+* ℂ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (c0 : Formalism.L2.DIV.VV K lam →ₛₗ[φ] W)
    (h : ∀ x y, inner ℂ (c0 x) (c0 y) = φ (pairV emb lam (-1) x y)) :
    ∀ x y, pairV emb lam (-1) x y = pairV emb lam 1 x y := by
  have hG : gramK emb (-1 : Matrix (Fin n) (Fin n) E) = fun τ => -(gramK emb 1 τ) := by
    funext τ
    ext i j
    simp [gramK, Matrix.neg_apply, Matrix.one_apply]
  have hneg : ∀ x y, pairV emb lam (-1) x y = negSign lam * pairV emb lam 1 x y := by
    intro x y
    unfold pairV
    rw [hG, pairK_neg]
  by_cases hnt : Nontrivial (Formalism.L2.DIV.VV K lam)
  · rcases mul_self_eq_one_iff.1 (negSign_mul_self (K := K) lam) with hc | hc
    · intro x y
      rw [hneg, hc, one_mul]
    · exfalso
      have hpos := Formalism.L2.DIV.pairPos K ι n lam (gramK emb 1) φ (fun τ => by
        have : ((gramK emb (1 : Matrix (Fin n) (Fin n) E) τ).map φ) = 1 := by
          ext i j
          simp [gramK, Matrix.one_apply]
        rw [this]
        exact Matrix.PosDef.one)
      obtain ⟨i⟩ := (bVV K lam).index_nonempty
      have h1 := hpos.diag_pos (i := i)
      simp only [Matrix.of_apply] at h1
      have h2 := h (bVV K lam i) (bVV K lam i)
      rw [hneg, hc, neg_one_mul, map_neg] at h2
      have h3 := inner_self_nonneg (𝕜 := ℂ) (x := c0 (bVV K lam i))
      rw [h2, map_neg, RCLike.re_to_complex] at h3
      have h4 := (Complex.lt_def.1 h1).1
      have h5 : (φ (pairV emb lam 1 (bVV K lam i) (bVV K lam i))).re =
          (φ (pairK lam (gramK emb 1) (bVV K lam i) (bVV K lam i))).re := rfl
      simp only [Complex.zero_re] at h4
      linarith
  · rw [not_nontrivial_iff_subsingleton] at hnt
    intro x y
    rw [Subsingleton.elim x 0]
    simp

end GlobalTheory.RowsSign

open GlobalTheory.RowsSign in
theorem GlobalTheory.RowsSign.pairV_gramR_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (c0R : Formalism.L2.DIV.VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W), cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) → Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) → (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) → ∀ x y, pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) gramR x y = pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) X.toD7.sp.X'.gram x y := by
  intro X px I hI cX gramR c0R hcX hg htie hinner x y
  have hJ : X.toD7.sp.X'.gram = 1 := by
    obtain ⟨hs, -, h2, -⟩ := hI.spaces
    change X.B.sp.X'.gram = 1
    rw [h2]
    refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
    simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]
  rcases hg with rfl | rfl
  · rfl
  · rw [hJ] at hinner ⊢
    exact pairV_neg_one_eq _ _ _ c0R hinner x y
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

namespace GlobalTheory.Mem.ColTie

theorem ipK_eq_card_mul_ipLev {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P) :
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  have h0 : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 := levelSumX W Ch sel mu P (mtildeOk W Ch sel mu hX P) (mtildeKOk W Ch sel mu hX) z.1 z'.1 z.2 z'.2
  unfold ipLev ipK
  rw [h1, mul_inv_cancel_left₀ h0]

end GlobalTheory.Mem.ColTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

def bar {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (q : PtY ST SG Q y) (w : SG) :
    Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal) :=
  {v | ∃ z ∈ q.1.2, v = q.1.1.deco.1.be w ((qOf w.1 : X.E) • z)}

def setStab {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) : Subgroup (GL (Fin n) κ) where
  carrier := {h | ∀ v, h.1 *ᵥ v ∈ C ↔ v ∈ C}
  one_mem' v := by simp
  mul_mem' {a b} ha hb v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  inv_mem' {a} ha v := by
    rw [← ha, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.MemChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatio
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_of_matEq {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) (y : GL (Fin b) A)
    (hm : MatEq x y) : y = castGL h x := by
  subst h
  ext i j
  simp only [castGL, Units.coe_mapEquiv, MulEquiv.coe_toMonoidHom]
  simp [Matrix.reindexAlgEquiv_apply]
  exact (hm.2 i j i j rfl rfl).symm

theorem matEq_castGL {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) : MatEq x (castGL h x) := by
  subst h
  refine ⟨rfl, fun i j i' j' hi hj => ?_⟩
  obtain rfl := Fin.ext hi
  obtain rfl := Fin.ext hj
  simp [castGL]

theorem castGL_mem_UA_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {a b : ℕ} (h : a = b) (x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.UA hc 1) :
    castGL h x ∈ Formalism.L2.DIV.UA hc 1 := by
  subst h
  have e : castGL (rfl : a = a) x = x := by
    ext i j
    simp [castGL]
  rwa [e]


set_option maxHeartbeats 1000000 in
theorem brgStdV_of_readsStd_one : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m), L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∀ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) →
    ∀ P : ∀ t, LiftBrg.PresL X I hX U Xg tr L cV i t, (∀ t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 (P t)) →
      (∀ t v, (P t).coef v = c v) → BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (P t).extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i hβ hgram c hc P hR hcoef
  unfold BrgStdV StdSide
  refine ⟨c, ?_, ?_, ?_, X.toD7.sp.cm, ?_⟩
  · intro γ γE g hr hm v
    have hg : g = castGL (rkEq X i).symm γE := castGL_of_matEq _ γE g hm
    subst hg
    exact hc γ γE hr v
  · intro hcm t φ h x hm
    refine ((hR t _ h).trans (hcoef t _)).trans ?_
    congr 1
    rw [Formalism.L2.Col.decoPt_mk]
    unfold ptL
    congr 1
    rw [hβ] at hm
    have hx := castGL_of_matEq (rkEq X i).symm _ _ hm
    rw [hx]
    simp only [matIn, mul_one, inv_one, one_mul, Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  · have hli := (P (Formalism.L2.DIV.mu0F _)).coef_li
    simp only [hcoef] at hli
    exact hli
  · intro h
    obtain ⟨g, hg⟩ := h.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) h.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hg]; exact GlobalTheory.LevSplit.finE_mem_UA _ g
    rw [hgram] at h1
    refine ⟨⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1), castGL_mem_UA_std _ _ _ h1⟩, ?_⟩
    rw [hβ]
    have hm := matEq_castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1)
    simp only [matIn, mul_one]
    exact hm

end GlobalTheory.Mem.R3.LiftBrg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdSideUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.StdUnique

theorem closed_eq_univ {D : D7} (V : HSp D) (C : Set (GA D V)) (hC : IsClosed C) (hQ : ∀ γ ∈ GQ V, γ ∈ C)
    (hf : ∀ h, ∀ k ∈ GfC V, h ∈ C → h * k ∈ C) (h : GA D V) : h ∈ C := by
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, (e h).2 = 1 → h ∈ GinfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))
  have hinf : ∀ h : GA D V, (e h).1 = 1 → h ∈ GfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).2.symm.trans (by rw [H]; rfl)))
  have hu : e.symm ((e h).1, 1) ∈ C := by
    by_contra hn
    obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V _ (hfin _ (by rw [e.apply_symm_apply])) Cᶜ
      hC.isOpen_compl hn
    exact hU (hf γ k hk (hQ γ hγ))
  have hk : e.symm (1, (e h).2) ∈ GfC V := hinf _ (by rw [e.apply_symm_apply])
  have := hf _ _ hk hu
  rwa [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply] at this

variable {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is)
include hc

theorem bot_or_top (U : Submodule ℂ c.W) (hU : ∀ γ ∈ GQ V, ∀ w ∈ U, c.ρ γ w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  refine hc.2.2.2.2 U fun h => ?_
  rintro _ ⟨w, hw, rfl⟩
  refine closed_eq_univ V {h | c.ρ h w ∈ U} (U.closed_of_finiteDimensional.preimage (hc.2.2.1 w))
    (fun γ hγ => hU γ hγ w hw) (fun h k hk H => ?_) h
  show c.ρ (h * k) w ∈ U
  rw [map_mul, hc.1 k hk, mul_one]
  exact H


omit hc in
theorem exists_ratMat (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
  exact ⟨g, hg.symm⟩

omit hc

end GlobalTheory.Mem.StdUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGamMemUJ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.step_gam_mem_UJ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (b : (I.stp u a i).β) (g : (I.stp u a i).G b), (I.stp u a i).gam b g ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) := by
  intro B X I hI hP l Z u a i hi b g
  have hG := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have hU := (hI.stp_ok u a i).unit b g
  show cT _ _ * _ * _ = _
  rw [hG, Matrix.mul_one]
  exact hU
end

