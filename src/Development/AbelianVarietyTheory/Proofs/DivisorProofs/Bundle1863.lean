module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
public import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.MkTauEmbInjective
public import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.SecJet

section Alg

variable (R : Type) [CommRing R]

def sqIdeal (k : ℕ) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range fun a : Fin k => (MvPolynomial.X a : MvPolynomial (Fin k) R) ^ 2)

abbrev EpsAlg (k : ℕ) : Type := MvPolynomial (Fin k) R ⧸ sqIdeal R k

def eps {k : ℕ} (a : Fin k) : EpsAlg R k := Ideal.Quotient.mk _ (MvPolynomial.X a)

theorem eps_mul_self {k : ℕ} (a : Fin k) : eps R a * eps R a = 0 := by
  rw [eps, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span ⟨a, rfl⟩

def epsIncl {k : ℕ} (a : Fin k) : DualNumber R →ₐ[R] EpsAlg R k :=
  DualNumber.lift ⟨(Algebra.ofId R (EpsAlg R k), eps R a), eps_mul_self R a,
    fun _ => Commute.all _ _⟩

end Alg

end GlobalTheory.SecJet

namespace GlobalTheory.SecJet

section Geo

variable (R : Type) [CommRing R]

abbrev epsT (k : ℕ) : Over (Sp R) := Over.mk (spMap (algebraMap R (EpsAlg R k)))

theorem spMap_comp_eq {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    spMap (f : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap

def epsIn {k : ℕ} (a : Fin k) : epsT R k ⟶ epsR R :=
  Over.homMk (spMap ((epsIncl R a : DualNumber R →ₐ[R] EpsAlg R k) : DualNumber R →+* EpsAlg R k))
    (spMap_comp_eq R (epsIncl R a))

def epsScaleA (c : R) : DualNumber R →ₐ[R] DualNumber R :=
  { epsScaleR c with commutes' := fun r => by simp [epsScaleR] }

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (spMap_comp_eq R (epsScaleA R c))

variable {R}

def tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) : epsR R ⟶ G :=
  (List.ofFn fun i => epsScale R (c i) ≫ v i).prod

theorem isLieComb_tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) :
    IsLieComb c v (tanComb c v) :=
  ⟨_, fun _ => rfl, rfl⟩

end Geo


open Classical in
def rigVal {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA]
    {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {N : ℕ} (w : LB.Iso (MM.L.pull φ) (lbPow P.L N))
    (i₀ : (lbPow P.L N).ι) : K :=
  if h : ∃ p : PUnit → MM.L.ι,
      ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) then
    valR (X := P.A.left) (eSec P.A) _ (w.s (i₀, h.choose)).val *
      valR (X := Sp (𝓞 K)) (spMap (algebraMap (𝓞 K) K)) _ (MM.rig.s h.choose).val
  else 0

end GlobalTheory.SecJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlace
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

section GenericCmp

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

theorem exists_smul_eq_sum_finBasis (x : L ⊗[O] M) : ∃ d : O, d ≠ 0 ∧ ∃ c : _ → L,
    d • x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing O) M a := by
  set v := Module.finBasis (FractionRing O) M
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, hd, c, e⟩ := hx
    obtain ⟨d', hd', c', e'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
    simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    conv_lhs => rw [← v.sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_eq_smul_of_read
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    (s t : L ⊗[O] M) (a : ℂ) (h : readExt rd eL hL s = a • readExt rd eL hL t) (h0 : readExt rd eL hL s ≠ 0) :
    ∃ b : L, eL b = a ∧ s = b • t := by
  set R := readExt rd eL hL with hR
  set v := Module.finBasis (FractionRing O) M
  have hne : ∀ d : O, d ≠ 0 → eL (algebraMap O L d) ≠ 0 := fun d hd => by
    rw [hL]
    exact (map_ne_zero eK).2 ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd)
  have hsm : ∀ (d : O) (x : L ⊗[O] M), R (d • x) = eL (algebraMap O L d) • R x := fun d x => by
    rw [← algebraMap_smul L d x, hR, readExt_smul]
  have hsum : ∀ c : _ → L, R (∑ k, c k ⊗ₜ v k) = ∑ k, eL (c k) • rd (v k) := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  obtain ⟨d, hd, c, es⟩ := exists_smul_eq_sum_finBasis s
  obtain ⟨d', hd', c', et⟩ := exists_smul_eq_sum_finBasis t
  have hcoef : ∀ k, eL (algebraMap O L d') * eL (c k) = a * (eL (algebraMap O L d) * eL (c' k)) := fun k => by
    have e1 : ∑ k, (eL (algebraMap O L d') * eL (c k) - a * (eL (algebraMap O L d) * eL (c' k))) • rd (v k) = 0 := by
      have h1 : eL (algebraMap O L d') • R (d • s) = a • eL (algebraMap O L d) • R (d' • t) := by
        rw [hsm, hsm, h]
        simp only [smul_smul]
        congr 1
        ring
      rw [es, et, hsum, hsum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [h1, sub_self]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ e1 k)
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h0
    have h2 : eL (algebraMap O L d) • R s = 0 := by
      rw [← hsm, es, hsum]
      simp [hc]
    exact (smul_eq_zero.1 h2).resolve_left (hne d hd)
  have hl : eL (algebraMap O L d') * eL (c k) ≠ 0 := mul_ne_zero (hne d' hd') ((map_ne_zero eL).2 hk)
  have hr : eL (algebraMap O L d) * eL (c' k) ≠ 0 := fun h3 => hl (by rw [hcoef k, h3, mul_zero])
  refine ⟨(algebraMap O L d' * c k) / (algebraMap O L d * c' k), ?_, ?_⟩
  · rw [map_div₀, map_mul, map_mul, hcoef k, mul_div_assoc, div_self hr, mul_one]
  · have hb : eL ((algebraMap O L d' * c k) / (algebraMap O L d * c' k)) = a := by
      rw [map_div₀, map_mul, map_mul, hcoef k, mul_div_assoc, div_self hr, mul_one]
    apply readExt_injective rd eL hL hF
    rw [readExt_smul, hb, ← hR, h]

end GenericCmp

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.SerBase


end GlobalTheory.BigOn.Exp.SerBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCmHostRootNeSelf
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.CovTop.WtRead

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [mul_self_nonneg H.rt0.re]

theorem exists_of_places (D : D7) (τ : D.host.E →+* ℂ) :
    ∃ t, DV.tauEmb D t = τ ∨ conjEmb (DV.tauEmb D t) = τ := by
  have hb : Function.Bijective fun t => InfinitePlace.mk (DV.tauEmb D t) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨Formalism.L2.Geo.Rec.StarEmbeddingNorm.mk_tauEmb_injective D, (Formalism.L2.Geo.Rec.StarEmbeddingNorm.card_places D).symm⟩
  obtain ⟨t, ht⟩ := hb.2 (InfinitePlace.mk τ)
  refine ⟨t, ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 ht with h | h
  · exact Or.inl h
  · right
    rw [← h]
    ext x
    simp [conjEmb, ComplexEmbedding.conjugate_coe_eq]

theorem tauEmb_bijective (D : D7) (Q : Par D) (hQ : Q.PinHost) :
    Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hQ.2.2.2 t⟩ : Psi Q.H)) := by
  refine ⟨fun s t h => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val h), fun τ => ?_⟩
  obtain ⟨t, h | h⟩ := exists_of_places D τ.1
  · exact ⟨t, Subtype.ext h⟩
  · exfalso
    have h1 : conjEmb (DV.tauEmb D t) (Q.H.rt : D.host.E) = (starRingEnd ℂ) Q.H.rt0 := by
      simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, hQ.2.2.2 t]
    exact conj_cmHostRoot_ne_self Q.H (h1.symm.trans ((congrArg (fun σ : D.host.E →+* ℂ => σ (Q.H.rt : D.host.E)) h).trans τ.2))

def tauPsi (D : D7) (Q : Par D) (hQ : Q.PinHost) : D.what₂.Tau ≃ Psi Q.H :=
  Equiv.ofBijective _ (tauEmb_bijective D Q hQ)

theorem sigW_add (D : D7) (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
  have := i.2
  unfold Ranks.sigW Ranks.r
  simp only
  omega

theorem laOf_big (D : D7) (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (t : D.what₂.Tau) (τ : Psi T.Q.H) (hτ : τ.1 = DV.tauEmb D t)
    (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)) (a : Fin (D.R.sigW ((i : ℕ) + 1)).1)
    (ha : (a : ℕ) = k) :
    laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n τ k = (κ.aP t a : ℤ) + ((κ.n / 2 : ℕ) : ℤ) := by
  have hD := hT.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hk : (k : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := by have := hD.1; have := a.2; omega
  simp only [laOf, weightOf, if_pos hk, hτ]
  rw [GlobalTheory.WeightExponents.wtA_tauEmb hT.pins.1, Formalism.L2.Pj.ext0, dite_eq_left (by omega)]
  have : (⟨(k : ℕ), by omega⟩ : Fin (D.R.sigW ((i : ℕ) + 1)).1) = a := Fin.ext ha.symm
  rw [this]

theorem laOf_small (D : D7) (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (t : D.what₂.Tau) (τ : Psi T.Q.H) (hτ : τ.1 = DV.tauEmb D t)
    (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)) (a : Fin (D.R.sigW ((i : ℕ) + 1)).2)
    (ha : (a : ℕ) + k + 1 = D.R.r) :
    laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n τ k = -(κ.aM t a : ℤ) - ((κ.n / 2 : ℕ) : ℤ) := by
  have hD := hT.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hs := sigW_add D i
  have hp := hD.1
  have hq := hD.2.1
  have hk : ¬ (k : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := by omega
  simp only [laOf, weightOf, if_neg hk, hτ]
  rw [GlobalTheory.Shares.WtDic.wtA_conj, Formalism.L2.Pj.ext0, dite_eq_left (by omega)]
  have : (⟨(T.Q.Dw ((i : ℕ) + 1)).q - 1 - ((k : ℕ) - (T.Q.Dw ((i : ℕ) + 1)).p), by omega⟩ :
      Fin (D.R.sigW ((i : ℕ) + 1)).2) = a := Fin.ext (by simp only; omega)
  rw [this]

theorem main : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 ∧ (T.Q.Dw ((i : ℕ) + 1)).q = (D.R.sigW ((i : ℕ) + 1)).2 ∧ Nat.card (Psi T.Q.H) = D.R.f ∧ dimFlag (T.Q.Dw ((i : ℕ) + 1)) = D.R.f * D.R.r.choose 2 ∧ Dom (wtA κ) κ.n ∧ ∃ e : D.what₂.Tau ≃ Psi T.Q.H, (∀ t, (e t).1 = DV.tauEmb D t) ∧ ∀ t (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)), (∀ a : Fin (D.R.sigW ((i : ℕ) + 1)).1, (a : ℕ) = k → laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n (e t) k = (κ.aP t a : ℤ) + ((κ.n / 2 : ℕ) : ℤ)) ∧ (∀ a : Fin (D.R.sigW ((i : ℕ) + 1)).2, (a : ℕ) + k + 1 = D.R.r → |laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n (e t) k + (κ.aM t a : ℤ)| ≤ (κ.n : ℤ)) := by
  intro D T hT i κ
  have hP := hT.pins
  have hD := hP.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hs := sigW_add D i
  have hcard : Fintype.card (Psi T.Q.H) = D.R.f :=
    (Fintype.card_congr (tauPsi D T.Q hP.1)).symm.trans (Formalism.MainNotions.Lnk.card_Tau D)
  refine ⟨hD.1, hD.2.1, ?_, ?_, Formalism.L2.Pj.dom_wtA κ, tauPsi D T.Q hP.1, fun t => rfl, fun t k => ⟨?_, ?_⟩⟩
  · rw [Nat.card_eq_fintype_card, hcard]
  · rw [dimFlag, Formalism.DegreeFormula.dimFl, hcard, hD.1, hD.2.1, hs, Nat.choose_two_right]
  · exact fun a ha => laOf_big D T hT i κ t _ rfl k a ha
  · intro a ha
    rw [laOf_small D T hT i κ t _ rfl k a ha]
    have h0 : (0 : ℤ) ≤ ((κ.n / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
    have h1 : ((κ.n / 2 : ℕ) : ℤ) ≤ (κ.n : ℤ) := by exact_mod_cast Nat.div_le_self _ _
    rw [show -(κ.aM t a : ℤ) - ((κ.n / 2 : ℕ) : ℤ) + (κ.aM t a : ℤ) = -((κ.n / 2 : ℕ) : ℤ) by ring, abs_neg,
      abs_of_nonneg h0]
    exact h1

end GlobalTheory.CovTop.WtRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeight
section
noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem archSec_exists_eq_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed (Xo := Xo) (c := c) →
    ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  intro E _ _ _ H Dw l Xo c r U x hU hF Z la s t
  obtain σ : c.F →+* ℂ := c.F.val.toRingHom
  have hσ₀ : GoodEmb c (goodOf c σ) := goodEmb_goodOf c σ
  set V := U (goodOf c σ) with hV

  have hinv : s.inv ∈ suppOn Z := by
    have h := mul_mem_suppOn s.inv (idem_mem_suppOn Z)
    rwa [mul_comm, s.idem_inv] at h
  have hg0 : t.sig * s.inv ∈ secZ Xo c 0 := by
    have h := mul_mem_secZ t.sig_mem s.inv_mem
    rwa [add_neg_cancel] at h
  have hgs : t.sig * s.inv ∈ suppOn Z := mul_mem_suppOn t.sig hinv

  have hb : ∀ z ∈ framesOn V Z, ‖rdU V (t.sig * s.inv) z.1 z.2‖ = t.cInf σ / s.cInf σ := by
    intro z hz
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ f : Rul Xo c, homN V x (wtOf Dw la 0) f z = ‖rdU V f z.1 z.2‖ * K := by
      refine ⟨lieFacZ Dw x (wtOf Dw la 0) *
        (V.X z.1).pnorm (modelWt V (wtOf Dw la 0) z.1) (fun _ => 1) z.2, fun f => ?_⟩
      simp only [homN, ptN, ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm, norm_one, one_mul]
      ring
    have ht : ‖rdU V t.sig z.1 z.2‖ * K = t.cInf σ := by
      rw [← hK]
      have h := t.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) t.sig) hz
      exact h
    have hs : ‖rdU V s.sig z.1 z.2‖ * K = s.cInf σ := by
      rw [← hK]
      have h := s.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) s.sig) hz
      exact h
    have hspos := s.cInf_pos σ
    have hs0 : rdU V s.sig z.1 z.2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_mul] at hs
      linarith
    have hread : ∀ f g : Rul Xo c, rdU V (f * g) z.1 z.2 = rdU V f z.1 z.2 * rdU V g z.1 z.2 := by
      intro f g
      rw [AllWt.rdU_mul]
      rfl
    have hidem : rdU V (idem Z) z.1 z.2 = 1 := by
      have h := congrArg (fun f => rdU V f z.1 z.2) s.idem_sig
      simp only [hread] at h
      exact (mul_eq_right₀ hs0).mp h
    have hone : rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2 = 1 := by
      rw [← hread, s.mul_inv, hidem]
    rw [eq_div_iff hspos.ne', ← hs, hread, norm_mul]
    calc ‖rdU V t.sig z.1 z.2‖ * ‖rdU V s.inv z.1 z.2‖ * (‖rdU V s.sig z.1 z.2‖ * K)
        = ‖rdU V t.sig z.1 z.2‖ * K * ‖rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2‖ := by
          rw [norm_mul]; ring
      _ = t.cInf σ := by rw [ht, hone, norm_one, mul_one]
  obtain ⟨a, ha⟩ := exists_eq_smul_idem V hσ₀ (hU _ hσ₀) hF hg0 hgs hb
  have hts : t.sig = s.sig * (t.sig * s.inv) := by
    calc t.sig = idem Z * t.sig := t.idem_sig.symm
      _ = s.sig * s.inv * t.sig := by rw [s.mul_inv]
      _ = s.sig * (t.sig * s.inv) := by ring
  have hsi : s.sig * idem Z = s.sig := by rw [mul_comm]; exact s.idem_sig
  have hta : t.sig = a • s.sig := by
    rw [hts, ha, mul_smul_comm, hsi]
  by_cases ha0 : a = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    have ht0 : t.sig = 0 := by
      set_option synthInstance.maxHeartbeats 200000 in
        rw [hta, ha0, zero_smul]
    have hi0 : idem Z = 0 := by rw [← t.mul_inv, ht0, zero_mul]
    have hs0 : s.sig = 0 := by rw [← s.idem_sig, hi0, zero_mul]
    rw [ht0, hs0, smul_zero]
  · exact ⟨a, ha0, hta⟩

end GlobalTheory.FlatCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRep
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem continuous_coef_piTensorMap {X ι : Type} [TopologicalSpace X] [Fintype ι] {M : ι → Type}
    [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)] [∀ c, Module.Finite ℂ (M c)]
    (f : X → ∀ c, M c →ₗ[ℂ] M c)
    (hf : ∀ c (x : M c) (ℓ : Module.Dual ℂ (M c)), Continuous fun g => ℓ (f g c x))
    (u : PiTensorProduct ℂ M) (ℓ : Module.Dual ℂ (PiTensorProduct ℂ M)) :
    Continuous fun g => ℓ (PiTensorProduct.map (f g) u) := by
  classical
  let bc := fun c => Module.Free.chooseBasis ℂ (M c)
  let B := Basis.piTensorProduct bc
  have key : ∀ k k', Continuous fun g => B.repr (PiTensorProduct.map (f g) (B k)) k' := by
    intro k k'
    simp only [B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
    exact continuous_finsetProd _ fun c _ => by
      simpa [Module.Basis.coord_apply] using hf c (bc c (k c)) ((bc c).coord (k' c))
  have h : ∀ g, ℓ (PiTensorProduct.map (f g) u) =
      ∑ k, ∑ k', B.repr u k * (B.repr (PiTensorProduct.map (f g) (B k)) k' * ℓ (B k')) := by
    intro g
    conv_lhs => rw [← B.sum_repr u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [← B.sum_repr (PiTensorProduct.map (f g) (B k))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  simp_rw [h]
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun k' _ =>
    continuous_const.mul ((key k k').mul continuous_const)

theorem continuous_coef_sqRep (n : ℕ) (mu : DomWeight n) (x : nablaSq ℂ n mu) (ℓ : Module.Dual ℂ (nablaSq ℂ n mu)) :
    Continuous fun a : GL (Fin n) ℂ => ℓ (GlobalTheory.Branching.sqRep ℂ n mu a x) := by
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.exists_coef_sqRep n mu x ℓ
  simp only [hP]
  exact (Units.continuous_val.matrix_det.zpow₀ _
      fun a : GL (Fin n) ℂ => Or.inl (Matrix.GeneralLinearGroup.det a).ne_zero).mul
    ((MvPolynomial.continuous_eval P).comp (continuous_pi fun i => Units.continuous_val.matrix_elem i.1 i.2))

theorem continuous_coef_wInf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)),
    Continuous fun g : UA E n => ℓ (wInf lam g u) := by
  intro E _ _ _ n lam u ℓ
  exact continuous_coef_piTensorMap
    (fun g v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding g))
    (fun v x ℓ' => (continuous_coef_sqRep n (lam v) x ℓ').comp (GlobalTheory.AutRec.continuous_cEmb_emb _)) u ℓ

end GlobalTheory.BCT.TrKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumConditionStableLatticeStabilizerIneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumCondition_stable_latticeStabilizer_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ₁)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ₁))) := by
  first | exact @GlobalTheory.DblVacTransport.acts_dblVacCond_of_mem_KAtD | exact GlobalTheory.DblVacTransport.acts_dblVacCond_of_mem_KAtD | (intros; apply GlobalTheory.DblVacTransport.acts_dblVacCond_of_mem_KAtD <;> assumption)
end

