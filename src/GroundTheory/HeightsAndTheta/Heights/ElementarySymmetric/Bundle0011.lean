module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineMu
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubInsertion
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.MuFrameExists
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

def MuFrameExists.Statement (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) : Prop :=
  ∀ z ∈ mcPts (mCoordIdeal D.y), Nonempty (MuFrameAt H z)

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.MuFrameNormIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

def MuFrameNormIndep.Statement (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) : Prop :=
  ∀ z ∈ D.Xo, ∀ d d' : MuFrameAt H z, d.norm = d'.norm

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.MuLineNormEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

def MuLineNormEq.Statement (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) : Prop :=
  ∀ z ∈ D.Xo, ∀ d : MuFrameAt H z, (muLine H).h z = d.norm

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

universe u w

section Combinatorics

end Combinatorics

section Snoc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

end Snoc

section Dim

end Dim

theorem InterNumCut.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hA : CutRestrLenExact.Statement.{u, w})
    (hB : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  _root_.UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.proof hF hA hB

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumTieX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

theorem InterNumTie.proof (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumTie.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp b hsub
  classical
  obtain ⟨j, hjp⟩ := hsub.relevant
  have hj : x j ≠ 0 := fun h0 => hjp (hsub.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.full k Ω N x pp hsub.isPrime hsub.homog hsub.le j hj hjp
  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  let y : Fin (N + 1) → Ip.ResidueField := fun i => ψ (ratio hj i)
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    change ψ (ratio hj i) = 0
    rw [h0, map_zero]
  have hpy : primeOf (S := k) y = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) y := hpy ▸ hsub.le
  have hsubW : IsSubvar y pp e := ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩
  have hyj : y j ≠ 0 := fun h0 => hjp (hpy ▸ (mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0))
  have hy0 : y ≠ 0 := fun h => hyj (congrFun h j)
  set I := pp.comap (oneBlock (S := k) (N := N)) with hI_def
  have hI : I = primeOfOne (S := k) y := by rw [primeOfOne, hpy]
  have hIp : NumbersDVR.IsMultiProjPrime I := hI ▸ isMultiProjPrime_primeOfOne y hy0
  have hIdim : FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, hI, HilbertPositive.ringKrullDim_primeOfOne, hpy,
      hsub.dim]
    simp
  let H : ℤ → ℤ := fun m => NumbersDVR.hilbFn I (fun _ : Unit => m)
  let R : ℤ → ℤ := fun m => restrLen pp (twistSys k x m)
  have hY : ∀ᶠ n : ℕ in atTop, restrLen pp (twistSys k y (n : ℤ)) = H n := by
    filter_upwards [TwistSections.full k _ N y hy0] with n hn
    rw [← hpy, SectionsOverLocalization.restrLen_primeOf_eq_finrank y hyj, hn, HilbertPositive.finrank_piece_eq_hilbFn, ← hI]
  obtain ⟨r₀, hr₀⟩ := RestrictTwist.full.1 k Ω N x _ y hxy hxy' 0
  have hXY := hRL k Ω N x _ y hxy hxy' pp e hsubW (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have hRH : ∀ᶠ n : ℕ in atTop, R n = H n := by
    filter_upwards [hY, hXY] with n h1 h2
    have e1 : (twistBundle k y 0).toSubSystem = twistSys k y 0 := rfl
    have e2 : (twistBundle k x 0).toSubSystem = twistSys k x 0 := rfl
    rw [e1, e2, twistSys_zero_twist, twistSys_zero_twist] at h2
    rw [← h1, h2]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hRH
  have hRH' : ∀ m : ℤ, (n₀ : ℤ) ≤ m → R m = H m := by
    intro m hm
    have h := hn₀ m.toNat (by omega)
    rwa [Int.toNat_of_nonneg (by omega)] at h
  let bs : Fin e → Unit → ℤ := fun i _ => b i
  have hMD := (FieldNumbers.MixedDiffConst.full k Unit (fun _ => Fin (N + 1)) I hIp.multiHomog hIp.relevant e
    hIdim).1 bs
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hMD
  set B : ℤ := ∑ i, b i with hB
  have hev : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => twistSys k x (b i)) c = NumbersDVR.intNum k I bs := by
    filter_upwards [eventually_ge_atTop (m₀ () - B).toNat,
      eventually_all.mpr fun T : Finset (Fin e) => eventually_ge_atTop ((n₀ : ℤ) - ∑ i ∈ T, b i).toNat]
      with c hc1 hc2
    rw [SectionsOverLocalization.interSum_twistSys, ← hm₀ (fun _ => (c : ℤ) + B)
      (fun u => by cases u; change m₀ () ≤ (c : ℤ) + B; omega), SectionsOverLocalization.mixedDiff_eq_sum]
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hsum : (∑ i ∈ Tᶜ, bs i) = fun _ : Unit => ∑ i ∈ Tᶜ, b i := by
      funext u
      rw [Finset.sum_apply]
    have hc : (n₀ : ℤ) ≤ ∑ i ∈ T, b i + c := by have := hc2 T; omega
    have hsplit := Finset.sum_add_sum_compl T b
    have hcard : Tᶜ.card = e - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    rw [show restrLen pp (twistSys k x (∑ i ∈ T, b i + c)) = H (∑ i ∈ T, b i + c) from hRH' _ hc, hsum, hcard]
    change (-1) ^ (e - T.card) * H (∑ i ∈ T, b i + c) =
      (-1) ^ (e - T.card) * NumbersDVR.hilbFn I ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i)
    have hfun : ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i) =
        fun _ : Unit => ∑ i ∈ T, b i + c := by
      funext u
      simp only [Pi.sub_apply]
      omega
    rw [hfun]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hev.mono fun c h => h.symm)).limUnder_eq

theorem InterNumTie.of_restrictQuot (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) :
    InterNumTie.Statement.{u, w} :=
  InterNumTie.proof (RestrLenRestrict.proof
    (SurjectiveClosed.proof Extension.full.{u, w, w} IdealTwistFamily.proof
      (TildeVanish.proof SerreVanish.full.{u, w})) hRQ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterSumTopVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

attribute [local instance] twistMonoid

theorem InterSumTopVanish.proof (hM : MixedTwistShift.Statement.{u, w}) : InterSumTopVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L hW
  classical
  set L₀ : Fin n → LineBundle k x := fun j => L (Fin.castSucc j) with hL₀
  have hdim : ringKrullDim (Poly k N ⧸ pp) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := hW.dim.le
  have hA := hM k Ω N x n pp hW.isPrime hW.homog hW.le hdim L₀ (L (Fin.last n)) 0
  have hB := hM k Ω N x n pp hW.isPrime hW.homog hW.le hdim L₀ (twistBundle k x 0) 0
  filter_upwards [hA, hB] with c hAc hBc
  have hL : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
      (fun j => (L₀ j).toSubSystem) (L (Fin.last n)).toSubSystem := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hL₀]
  rw [interSum_eq_mixDiff, hL, mixDiff_snoc]
  have eA : mixDiff (fun g => restrLen pp (((L (Fin.last n)).toSubSystem * g).twist (twistSys k x (c : ℤ))))
      (fun j => (L₀ j).toSubSystem) =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen pp (((tensorSub (fun i => (L₀ i).toSubSystem) T).twist (L (Fin.last n)).toSubSystem).twist
          (twistSys k x ((c : ℤ) + 0))) := by
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    have hc : (L (Fin.last n)).toSubSystem * ∏ j ∈ T, (L₀ j).toSubSystem =
        (∏ j ∈ T, (L₀ j).toSubSystem).twist (L (Fin.last n)).toSubSystem := SubSystem.twist_comm _ _
    rw [tensorSub_eq_prod, add_zero]
    beta_reduce
    rw [hc]
  have eB : mixDiff (fun F => restrLen pp (F.twist (twistSys k x (c : ℤ)))) (fun j => (L₀ j).toSubSystem) =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen pp (((tensorSub (fun i => (L₀ i).toSubSystem) T).twist (twistBundle k x 0).toSubSystem).twist
          (twistSys k x ((c : ℤ) + 0))) := by
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    have hz : (∏ j ∈ T, (L₀ j).toSubSystem).twist (twistBundle k x 0).toSubSystem =
        ∏ j ∈ T, (L₀ j).toSubSystem := SubSystem.twist_twistSys_zero _
    rw [tensorSub_eq_prod, add_zero]
    beta_reduce
    rw [hz]
  rw [eA, eB, hAc, hBc, sub_self]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMixedTwistShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace MixedTwistShiftAlt

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | i :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem prod_map_filter {R : Type*} [CommMonoid R] {n : ℕ} (g : Fin n → R) (T : Finset (Fin n)) :
    ∀ l : List (Fin n),
      ((l.filter (· ∈ T)).map g).prod = (l.map fun j => g j ^ (if j ∈ T then 1 else 0)).prod
  | [] => rfl
  | j :: l => by
    by_cases hj : j ∈ T <;> simp [hj, prod_map_filter g T l]

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = ∏ j, (L j).sub I ^ (if j ∈ T then 1 else 0) := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [tensorSub, foldl_twist_sub, h0, one_mul, prod_map_filter, Fin.prod_univ_def]

theorem twistPows_snoc_sub {n : ℕ} (L : Fin n → LineBundle k x) (M : LineBundle k x) (T : Finset (Fin n))
    (m : ℕ) (I : Chart x) :
    ((twistSys k x 0).twistPows (n + 1)
        (fun j => (Fin.snoc (α := fun _ => LineBundle k x) L M j).toSubSystem)
        (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m)).sub I =
      M.sub I ^ m * (tensorSub (fun i => (L i).toSubSystem) T).sub I := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [SnapperSections.twistPows_sub, tensorSub_sub, h0, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

end MixedTwistShiftAlt


open MixedTwistShiftAlt in
theorem MixedTwistShift.proof (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) (hR : RestrLenEuler.Statement.{u, w}) (hD : SubsetDiffConst.Statement) :
    MixedTwistShift.Statement.{u, w} := by
  intro k _ Ω _ _ N x n qq hp hh hle hdim L M d
  set L' : Fin (n + 1) → LineBundle k x := Fin.snoc (α := fun _ => LineBundle k x) L M with hL'
  set ν : Finset (Fin n) → ℕ → Fin (n + 1) → ℕ :=
    fun T m => Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m with hν
  set f : (Fin (n + 1) → ℕ) → ℤ → ℚ := fun e c => (pieceChar k qq 0 L' e c : ℚ) with hf
  set Ls : Fin n → SubSystem k x Ω := fun i => (L i).toSubSystem with hLs

  have hA : ∀ T (c : ℤ), ((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 1)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, SubSystem.twist_sub_eq_mul_of_line, pow_one]
  have hB : ∀ T (c : ℤ), (tensorSub Ls T).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 0)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, pow_zero, one_mul]

  have hev : ∀ m : ℕ, ∀ᶠ c : ℤ in atTop, ∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c :=
    fun m => eventually_all.2 fun T => hR k Ω N x qq hh hle (n + 1) L' (ν T m)
  have hsum : ∀ (m : ℕ) (c : ℤ), (∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c) →
      ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
          (twistSys k x c)) : ℤ) : ℚ) = subsetDiff n f m c := by
    intro m c h
    rw [subsetDiff]
    push_cast
    exact Finset.sum_congr rfl fun T _ => by rw [h T]
  obtain ⟨hconst, hzero⟩ := hD n f (pieceChar_isNumPolyLT hH hS hP L' (n + 1) qq hp hh hle hdim 0)
  have hT1 : Tendsto (fun c : ℕ => (c : ℤ) + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d tendsto_natCast_atTop_atTop
  have hLhs : ∀ᶠ c : ℕ in atTop, ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
      restrLen qq (((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x ((c : ℤ) + d))) : ℤ) : ℚ) =
        subsetDiff n f 1 ((c : ℤ) + d) := by
    filter_upwards [hT1.eventually (hev 1)] with c hc
    simp only [hA]
    exact hsum 1 _ hc
  split_ifs with hW
  ·
    have hI : ∀ᶠ c : ℕ in atTop, (interSum qq Ls c : ℚ) = subsetDiff n f 0 (c : ℤ) := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (hev 0)] with c hc
      rw [interSum]
      simp only [hB]
      exact hsum 0 _ hc
    obtain ⟨c₀, hc₀⟩ := hI.exists_forall_of_atTop
    have hκ : ∀ᶠ c : ℕ in atTop, interSum qq Ls c = interSum qq Ls c₀ := by
      filter_upwards [eventually_ge_atTop c₀] with c hc
      exact_mod_cast (hc₀ c hc).trans ((hconst 0 0 c c₀).trans (hc₀ c₀ le_rfl).symm)
    have hlim : interNum qq Ls = interSum qq Ls c₀ :=
      (tendsto_const_nhds.congr' (hκ.mono fun _ hc => hc.symm)).limUnder_eq
    rw [hlim]
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans ((hconst 1 0 _ c₀).trans (hc₀ c₀ le_rfl).symm)
  ·
    have hlow : IsNumPolyLT (n + 1) n f := by
      by_cases hrel : ∃ i, (X i : Poly k N) ∉ qq
      · have := hp
        obtain ⟨e, he⟩ := SnapperSections.exists_dim_eq qq hh hrel
        have hen : e ≠ n := fun h => hW ⟨hp, hh, hle, hrel, by subst h; exact he⟩
        have hle' : e + 1 ≤ n + 1 := by
          rw [he] at hdim
          exact_mod_cast hdim
        refine pieceChar_isNumPolyLT hH hS hP L' n qq hp hh hle ?_ 0
        rw [he]
        exact_mod_cast (by omega : e + 1 ≤ n)
      · push Not at hrel
        exact ⟨0, Or.inl rfl, fun e c => by simp [hf, pieceChar_of_irrelevant qq hrel]⟩
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans (hzero hlow 1 _)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

