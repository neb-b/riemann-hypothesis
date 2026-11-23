module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import ReciprocityTheory.AdeleApproximation.AdeleIntA

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Topology Filter
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tate

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

end Tate

section Matrix

variable {D : D7} (S T : HSp D)

theorem embedding_xi_zero_ne_zero : D.host.xi0 ≠ 0 := by
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hdpos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    have : (Real.sqrt D.host.d : ℂ) = 0 := by
      rcases mul_eq_zero.1 hd.symm with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    exact (Real.sqrt_pos.2 hdpos).ne' (by exact_mod_cast this)
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  unfold Host.xi0
  exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hN hs)

def hE (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  ∑ a, ∑ b, ∑ c, ∑ d, S.gram⁻¹ a b * star (γ c b) * T.gram c d * e d a

def betaO (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.F :=
  Algebra.trace D.host.F D.host.E (D.host.xi0 * hE S T e γ)

theorem symplO_ratW_ratW (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (ratW T S e) (ratW T S γ) = algebraMap D.host.F (AF D.host.F) (betaO S T e γ) := by
  have h : hO S T (ratW T S e) (ratW T S γ) = incA D (hE S T e γ) := by
    unfold hO hE
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, ratW, Matrix.map_apply, Brg.cA_inc]
  unfold symplO betaO
  rw [h, ← map_mul, trace_incA]

theorem symplO_smul_left (c : AF D.host.F) (x y : WO S T) : symplO S T (c • x) y = c * symplO S T x y := by
  have h : hO S T (c • x) y = algebraMap (AF D.host.F) (AE D) c * hO S T x y := by
    unfold hO
    simp only [Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring
  unfold symplO
  rw [h, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

end Matrix

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSplitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem psi_neg_one (ψ : AddChar (AF D.host.F) ℂ) {a : AF D.host.F} (h : ψ a = 1) : ψ (-a) = 1 := by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

variable (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem heisO_zero (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO_zero_right]

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.UniqPlugPl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
  IsDedekindDomain NumberField Topology Filter Formalism.IndefR.Fin.U1

namespace Formalism.IndefR.Fin.Refl

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {x y : AF F} (h1 : ∀ w, x.1 w = y.1 w) (h2 : ∀ v, x.2 v = y.2 v) : x = y := Prod.ext (funext h1) (by ext v; exact congrArg _ (h2 v))

def piF (v : HeightOneSpectrum (𝓞 F)) : AF F →+* v.adicCompletion F where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def piI (w : InfinitePlace F) : AF F →+* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def jF (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : AF F := pairA F 0 (single v y)


open Classical in
def jI (w : InfinitePlace F) (y : w.Completion) : AF F :=
  pairA F (Pi.single w y : ∀ w : InfinitePlace F, w.Completion) 0

theorem jF_fst (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) (w : InfinitePlace F) : (jF v y).1 w = 0 := rfl
theorem jF_self (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : (jF v y).2 v = y := by
  classical
  show (Pi.single v y : ∀ v' : HeightOneSpectrum (𝓞 F), v'.adicCompletion F) v = y
  exact Pi.single_eq_same v y
theorem jF_ne {v v' : HeightOneSpectrum (𝓞 F)} (y : v.adicCompletion F) (h : v' ≠ v) : (jF v y).2 v' = 0 := by
  classical
  show (Pi.single v y : ∀ v'' : HeightOneSpectrum (𝓞 F), v''.adicCompletion F) v' = 0
  exact Pi.single_eq_of_ne h y
theorem jI_snd (w : InfinitePlace F) (y : w.Completion) (v : HeightOneSpectrum (𝓞 F)) : (jI w y).2 v = 0 := rfl
open Classical in
theorem jI_self (w : InfinitePlace F) (y : w.Completion) : (jI w y).1 w = y := by simp [jI, pairA]
open Classical in
theorem jI_ne {w w' : InfinitePlace F} (y : w.Completion) (h : w' ≠ w) : (jI w y).1 w' = 0 := by simp [jI, pairA, Pi.single_eq_of_ne h]

theorem mul_jF (v : HeightOneSpectrum (𝓞 F)) (a : AF F) (y : v.adicCompletion F) :
    a * jF v y = jF v (piF v a * y) := by
  refine af_ext (fun w => ?_) (fun v' => ?_)
  · show a.1 w * (jF v y).1 w = (jF v (piF v a * y)).1 w
    rw [jF_fst, jF_fst, mul_zero]
  · show a.2 v' * (jF v y).2 v' = (jF v (piF v a * y)).2 v'
    by_cases h : v' = v
    · subst h
      rw [jF_self, jF_self]
      rfl
    · rw [jF_ne _ h, jF_ne _ h, mul_zero]

theorem mul_jI (w : InfinitePlace F) (a : AF F) (y : w.Completion) : a * jI w y = jI w (piI w a * y) := by
  refine af_ext (fun w' => ?_) (fun v => ?_)
  · show a.1 w' * (jI w y).1 w' = (jI w (piI w a * y)).1 w'
    by_cases h : w' = w
    · subst h
      rw [jI_self, jI_self]
      rfl
    · rw [jI_ne _ h, jI_ne _ h, mul_zero]
  · show a.2 v * (jI w y).2 v = (jI w (piI w a * y)).2 v
    rw [jI_snd, jI_snd, mul_zero]

theorem tendsto_fin {α : Type*} {l : Filter α} (z : α → Af F)
    (h : ∀ N : ℕ, N ≠ 0 → ∀ᶠ t in l, ∀ v, ‖z t v‖ ≤ ‖(N : v.adicCompletion F)‖) : Tendsto z l (𝓝 0) := by
  intro U hU
  obtain ⟨N, hN, hNU⟩ := finNhd U hU
  rw [Filter.mem_map]
  filter_upwards [h N (by omega)] with t ht
  obtain ⟨y, hy, e⟩ := int_of_le (z t) N 1 (by omega) fun v => by rw [Nat.cast_one, norm_one, mul_one]; exact ht v
  show z t ∈ U
  rw [e]; exact hNU y hy

theorem continuous_single (v : HeightOneSpectrum (𝓞 F)) : Continuous (single v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let s' : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal {v}ᶜ) :=
    fun y => RestrictedProduct.mk (Pi.single v y) (by
      rw [Filter.eventually_principal]
      intro w hw
      rw [Set.mem_compl_singleton_iff] at hw
      rw [Pi.single_eq_of_ne hw]
      exact zero_mem _)
  have hs' : Continuous s' := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases h : w = v
    · subst h
      show Continuous (fun y : w.adicCompletion F =>
        (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F) w)
      simp only [Pi.single_eq_same]
      exact continuous_id
    · show Continuous (fun y : v.adicCompletion F =>
        (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F) w)
      simp only [Pi.single_eq_of_ne h]
      exact continuous_const
  exact (RestrictedProduct.continuous_inclusion hS).comp hs'

theorem continuous_jF (v : HeightOneSpectrum (𝓞 F)) : Continuous (jF v) := continuous_const.prodMk (continuous_single v)

open Classical in
theorem continuous_jI (w : InfinitePlace F) : Continuous (jI w) := (_root_.continuous_single w).prodMk continuous_const

theorem dense_F (v : HeightOneSpectrum (𝓞 F)) : DenseRange fun q : F => piF v (algebraMap F (AF F) q) := by
  have h : (fun q : F => piF v (algebraMap F (AF F) q)) = algebraMap F (v.adicCompletion F) := by
    funext q
    show (algebraMap F (AF F) q).2 v = _
    rw [algebraMap_AF]
    rfl
  rw [h]
  exact HeightOneSpectrum.denseRange_algebraMap F v

theorem dense_I (w : InfinitePlace F) : DenseRange fun q : F => piI w (algebraMap F (AF F) q) := by
  have h : (fun q : F => piI w (algebraMap F (AF F) q)) = fun x : F => (x : w.Completion) := by
    funext q
    show (algebraMap F (AF F) q).1 w = _
    rw [algebraMap_AF]
    exact InfiniteAdeleRing.algebraMap_apply F q w
  rw [h]
  have e : Set.range (fun x : F => ((WithAbs.toAbs w.1 x : WithAbs w.1) : w.Completion)) =
      Set.range (fun x : WithAbs w.1 => (x : w.Completion)) :=
    (WithAbs.toAbs_surjective w.1).range_comp (fun x : WithAbs w.1 => (x : w.Completion))
  unfold DenseRange
  erw [e]
  exact AbsoluteValue.Completion.denseRange_coe w.1

def etaS (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F := ∑ w : InfinitePlace F, jI w 1 + ∑ v ∈ S, jF v 1

theorem etaS_fst (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) : piI w (etaS S) = 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [etaS, map_add (f := _), map_sum, map_sum, Finset.sum_eq_single w]
  · rw [show piI w (jI w 1) = (jI w 1).1 w from rfl, jI_self]
    simp only [show ∀ v, piI w (jF v 1) = (jF v 1).1 w from fun v => rfl, jF_fst, Finset.sum_const_zero, add_zero]
  · intro w' _ hw'
    show (jI w' 1).1 w = 0
    exact jI_ne _ (Ne.symm hw')
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem etaS_in (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
    piF v (etaS S) = 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [etaS, map_add (f := _), map_sum, map_sum, Finset.sum_eq_single v]
  · simp only [show ∀ w, piF v (jI w 1) = (jI w 1).2 v from fun w => rfl, jI_snd, Finset.sum_const_zero, zero_add]
    show (jF v 1).2 v = 1
    exact jF_self v 1
  · intro v' _ hv'
    show (jF v' 1).2 v = 0
    exact jF_ne _ (Ne.symm hv')
  · intro h
    exact absurd hv h

theorem etaS_out (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    piF v (etaS S) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [etaS, map_add (f := _), map_sum, map_sum]
  simp only [show ∀ w, piF v (jI w 1) = (jI w 1).2 v from fun w => rfl, jI_snd, Finset.sum_const_zero, zero_add]
  refine Finset.sum_eq_zero fun v' hv' => ?_
  show (jF v' 1).2 v = 0
  exact jF_ne _ (fun h => hv (h ▸ hv'))

theorem tendsto_etaS (a : AF F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => etaS S * a) atTop (𝓝 a) := by
  classical
  have h1 : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (etaS S * a).1 = a.1 := fun S => funext fun w => by
    show piI w (etaS S) * a.1 w = a.1 w
    rw [etaS_fst, one_mul]
  have h2 : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (etaS S * a).2 - a.2) atTop (𝓝 0) := by
    refine tendsto_fin _ fun N hN => ?_
    obtain ⟨S1, hS1⟩ := exists_finset_norm_one (N : F) (Nat.cast_ne_zero.2 hN)
    have hfin := Filter.eventually_cofinite.mp a.2.2
    filter_upwards [Filter.eventually_ge_atTop (S1 ∪ hfin.toFinset)] with S hS v
    show ‖piF v (etaS S) * a.2 v - a.2 v‖ ≤ _
    by_cases hv : v ∈ S
    · rw [etaS_in S v hv, one_mul, sub_self, norm_zero]; exact norm_nonneg _
    · have hv1 : v ∉ S1 := fun h => hv (hS (Finset.mem_union_left _ h))
      have hv2 : v ∉ hfin.toFinset := fun h => hv (hS (Finset.mem_union_right _ h))
      have hN1 := hS1 v hv1
      rw [map_natCast] at hN1
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv2
      rw [etaS_out S v hv, zero_mul, zero_sub, norm_neg, hN1]
      exact (norm_le_one_iff_int v _).2 hv2
  have h3 : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ((a.1, (etaS S * a).2) : Ainf F × Af F)) atTop
      (𝓝 (a.1, a.2)) := tendsto_const_nhds.prodMk_nhds (tendsto_sub_nhds_zero_iff.1 h2)
  have h4 : (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ((a.1, (etaS S * a).2) : Ainf F × Af F)) =
      fun S => etaS S * a := funext fun S => Prod.ext (h1 S).symm rfl
  rw [h4] at h3
  exact h3

end Formalism.IndefR.Fin.Refl

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.VacExA
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 400000

namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDyIdem (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop :=
  IsSplitIdem D e ∧ finPart D e ∈ intAE D ∧
    ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε


theorem fstA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : fstA D.host.F (pairA D.host.F x y) = x := rfl
theorem sndA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : sndA D.host.F (pairA D.host.F x y) = y := rfl



section Sym

variable (S T : HSp D)

end Sym

section Phi

variable (S T : HSp D)

def U0 (Λ : AddSubgroup (WO S T)) : AddSubgroup (WO S T) where
  carrier := {w | ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0}
  add_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u + u', Λ.add_mem hu hu', fun i j => ?_⟩
    have : (a + b - (u + u')) i j = (a - u) i j + (b - u') i j := by
      simp only [Matrix.sub_apply, Matrix.add_apply]; abel
    rw [this, map_add (f := _), ha, hb, add_zero]
  zero_mem' := ⟨0, Λ.zero_mem, fun i j => by simp⟩
  neg_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨-u, Λ.neg_mem hu, fun i j => ?_⟩
    have : (-a - -u) i j = -((a - u) i j) := by simp only [Matrix.sub_apply, Matrix.neg_apply]; abel
    rw [this, map_neg, ha, neg_zero]

theorem mem_U0 {Λ : AddSubgroup (WO S T)} {w : WO S T} :
    w ∈ U0 S T Λ ↔ ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0 := Iff.rfl

theorem le_open_neighbourhood {Λ : AddSubgroup (WO S T)} : Λ ≤ U0 S T Λ := fun u hu => ⟨u, hu, fun i j => by simp⟩

theorem open_neighbourhood_set_eq (Λ : AddSubgroup (WO S T)) :
    (U0 S T Λ : Set (WO S T)) = {w | ∃ u ∈ Λ, (w - u).map (finPart D) = 0} := by
  ext w
  simp only [SetLike.mem_coe, mem_U0, Set.mem_setOf_eq]
  refine exists_congr fun u => and_congr_right fun _ => ⟨fun h => ?_, fun h i j => ?_⟩
  · ext i j; exact h i j
  · have := congrFun (congrFun h i) j; simpa using this


end Phi

section Lat

variable (S T : HSp D)

variable {S T}

end Lat

end Formalism.IndefR.Fin.VacEx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.VacExApp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC Formalism.IndefR.Eqv
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

end Gen

variable {D : D7}

theorem AF_ext' {p q : AF D.host.F} (h1 : fstA D.host.F p = fstA D.host.F q) (h2 : sndA D.host.F p = sndA D.host.F q) :
    p = q :=
  Prod.ext h1 h2

theorem expand_cE (z : AE D) :
    z = ∑ k, (cE D.host.F D.host.E z k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) := by
  conv_lhs => rw [← (bA D.host.F D.host.E).sum_equivFun z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

def Ps (m n : ℕ) (p : Fin m → Fin n → Fin (nE D) → AF D.host.F) : Mx D m n :=
  Matrix.of fun i j => (cE D.host.F D.host.E).symm (p i j)

theorem continuous_Ps {m n : ℕ} : Continuous (Ps (D := D) m n) :=
  continuous_matrix fun i j =>
    (cE D.host.F D.host.E).symm.continuous.comp ((continuous_apply j).comp (continuous_apply i))

def boxB (D : D7) (m n : ℕ) : Set (Mx D m n) :=
  Ps m n '' Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
    (fun a : Af D.host.F => pairA D.host.F 0 a) '' Ohat D.host.F

theorem isCompact_boxB (m n : ℕ) : IsCompact (boxB D m n) := by
  have hc : Continuous fun a : Af D.host.F => pairA D.host.F 0 a := by
    unfold pairA; exact continuous_const.prodMk continuous_id
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    (isCompact_Ohat D.host.F).image hc).image continuous_Ps

theorem nsmul_pairA (N : ℕ) (a : Af D.host.F) : N • pairA D.host.F 0 a = pairA D.host.F 0 (N • a) := by
  refine AF_ext' ?_ ?_
  · rw [map_nsmul]; show N • (0 : Ainf D.host.F) = 0; exact nsmul_zero N
  · rw [map_nsmul]; rfl

end Formalism.IndefR.Fin.VacEx
end
end

