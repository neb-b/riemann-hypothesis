module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.IntMatIsCompact
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

theorem intMat_isOpen (m n : ℕ) :
    IsOpen {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} := by
  have e : {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} =
      ⋂ i, ⋂ j, (fun w : Matrix (Fin m) (Fin n) (AfE D) => w i j) ⁻¹' (intAE D : Set (AfE D)) := by
    ext w; simp
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))

theorem intMat_isCompact (m n : ℕ) :
    IsCompact {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} :=
  isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D

theorem U_isOpen {S : Finset (Pl D)} {ef : AfE D} (hef : ef ∈ intAE D) (N m n : ℕ) :
    IsOpen (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  refine AddSubgroup.isOpen_of_mem_nhds (U S ef N m n) (g := 0) ?_
  refine Filter.mem_of_superset ((intMat_isOpen m n).mem_nhds fun i j => zero_mem _) fun w hw => ?_
  exact ⟨fun v _ i j => cf_mem_of_mem (hw i j) v, fun i j =>
    GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE N)
      (GlobalTheory.HostAdeleIso.intAE_mul_mem D hef (hw i j))⟩

open Classical in
theorem U_isCompact {S : Finset (Pl D)} {ef : AfE D} (hef : ef ∈ intAE D)
    (hS : ∀ v : Pl D, cf v ef = if v ∈ S then 1 else 0) {N : ℕ} (hN : 0 < N) (m n : ℕ) :
    IsCompact (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hcl : IsClosed (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) :=
    AddSubgroup.isClosed_of_isOpen _ (U_isOpen hef N m n)
  let c : AfE D := algebraMap D.host.F (AfE D) ((N : D.host.F)⁻¹)
  have hc : c * (N : AfE D) = 1 := by
    have hN' : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [← map_natCast (algebraMap D.host.F (AfE D)) N, ← map_mul, inv_mul_cancel₀ hN', map_one]
  have hK : IsCompact ((fun w : Matrix (Fin m) (Fin n) (AfE D) => Matrix.of fun i j => c * w i j) ''
      {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D}) :=
    (intMat_isCompact m n).image (continuous_pi fun i => continuous_pi fun j =>
      continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
  refine hK.of_isClosed_subset hcl fun w hw => ?_
  refine ⟨Matrix.of fun i j => (N : AfE D) * w i j, fun i j => ?_, ?_⟩
  · have h1 : (1 - ef) * w i j ∈ intAE D := mem_of_cf_mem fun v => by
      rw [map_mul, map_sub, map_one, hS v]
      by_cases hv : v ∈ S
      · rw [if_pos hv, sub_self, zero_mul]; exact zero_mem _
      · rw [if_neg hv, sub_zero, one_mul]; exact hw.1 v hv i j
    have h2 : (N : AfE D) * w i j = (N : AfE D) * (ef * w i j) + (N : AfE D) * ((1 - ef) * w i j) := by ring
    rw [Matrix.of_apply, h2]
    exact add_mem (hw.2 i j) (GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE N) h1)
  · ext i j
    simp only [Matrix.of_apply]
    rw [← mul_assoc, hc, one_mul]

end PositivityTheory.Rg.Rsw.L.LBumpEx

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.IntegralBlockMatrixIff
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {D : D7}

def IntM {D : D7} {m p : ℕ} (v : Pl D) (M : Mx D m p) : Prop := ∀ i j, cv D v (M i j) ∈ intLoc D.host.F D.host.E v

namespace IntM

variable {v : Pl D} {m p q : ℕ}

theorem add {M N : Mx D m p} (hM : IntM v M) (hN : IntM v N) : IntM v (M + N) := fun i j => by
  rw [Matrix.add_apply, map_add (f := _)]; exact add_mem (hM i j) (hN i j)

theorem neg {M : Mx D m p} (hM : IntM v M) : IntM v (-M) := fun i j => by
  rw [Matrix.neg_apply, map_neg]; exact neg_mem (hM i j)

theorem zero : IntM v (0 : Mx D m p) := fun i j => by
  rw [Matrix.zero_apply, map_zero]; exact zero_mem _

theorem one : IntM v (1 : Mx D m m) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · rw [map_one]; exact one_mem _
  · rw [map_zero]; exact zero_mem _

theorem mul {M : Mx D m p} {N : Mx D p q} (hM : IntM v M) (hN : IntM v N) : IntM v (M * N) := fun i j => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun k _ => by rw [map_mul]; exact mul_mem (hM i k) (hN k j)

theorem inv {M : Mx D m m} (hM : IntM v M) (hu : IsUnit M.det)
    (hdet : ∃ z ∈ intLoc D.host.F D.host.E v, cv D v M.det * z = 1) : IntM v M⁻¹ := by
  obtain ⟨z, hz, hdz⟩ := hdet
  obtain ⟨u, hu'⟩ := hu
  have hinv : cv D v (Ring.inverse M.det) = z := by
    rw [← hu', Ring.inverse_unit]
    have h1 : cv D v ((u⁻¹ : (AE D)ˣ) : AE D) * cv D v (u : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu'] at h1
    calc cv D v ((u⁻¹ : (AE D)ˣ) : AE D) = cv D v ((u⁻¹ : (AE D)ˣ) : AE D) * (cv D v M.det * z) := by
          rw [hdz, mul_one]
      _ = z := by rw [← mul_assoc, h1, one_mul]

  let N : Matrix (Fin m) (Fin m) (intLoc D.host.F D.host.E v) := fun i j => ⟨cv D v (M i j), hM i j⟩
  have hN : N.map (intLoc D.host.F D.host.E v).subtype = M.map (cv D v) := rfl
  have hadj : ∀ i j, cv D v (M.adjugate i j) ∈ intLoc D.host.F D.host.E v := by
    intro i j
    have e1 : cv D v (M.adjugate i j) = (M.map (cv D v)).adjugate i j :=
      congrFun (congrFun (RingHom.map_adjugate (cv D v) M) i) j
    have e2 : (intLoc D.host.F D.host.E v).subtype (N.adjugate i j) =
        (N.map (intLoc D.host.F D.host.E v).subtype).adjugate i j :=
      congrFun (congrFun (RingHom.map_adjugate (intLoc D.host.F D.host.E v).subtype N) i) j
    rw [e1, ← hN, ← e2]
    exact (N.adjugate i j).2
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, hinv]
  exact mul_mem hz (hadj i j)

end IntM

theorem integral_block_matrix_iff {v : Pl D} {n : ℕ} {a b c d : Mx D n n} :
    IntM v (blk4 a b c d) ↔ IntM v a ∧ IntM v b ∧ IntM v c ∧ IntM v d := by
  have key : ∀ x y, blk4 a b c d (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks a b c d x y := by
    intro x y; simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · have := h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
      rwa [key, Matrix.fromBlocks_apply₁₁] at this
    · have := h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
      rwa [key, Matrix.fromBlocks_apply₁₂] at this
    · have := h (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j))
      rwa [key, Matrix.fromBlocks_apply₂₁] at this
    · have := h (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
      rwa [key, Matrix.fromBlocks_apply₂₂] at this
  · rintro ⟨ha, hb, hc, hd⟩ i j
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    show cv D v (blk4 a b c d _ _) ∈ _
    rw [key]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [Matrix.fromBlocks_apply₁₁]; exact ha i' j'
    · rw [Matrix.fromBlocks_apply₁₂]; exact hb i' j'
    · rw [Matrix.fromBlocks_apply₂₁]; exact hc i' j'
    · rw [Matrix.fromBlocks_apply₂₂]; exact hd i' j'

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKD
section
noncomputable section

open scoped TensorProduct NNReal
open Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cj_fromBlocks {R : Type} [CommRing R] (s : R →+* R) (a b c d : Matrix n n R) :
    cj s (fromBlocks a b c d) = fromBlocks (cj s a) (cj s c) (cj s b) (cj s d) := by
  unfold cj
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cj_neg {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) : cj s (-M) = -cj s M := by
  ext i j; simp [cj]

theorem cj_zero {R : Type} [CommRing R] (s : R →+* R) {m p : Type} : cj s (0 : Matrix m p R) = 0 := by
  ext i j; simp [cj]

theorem unit_rel {R : Type} [CommRing R] (s : R →+* R) (a b c d : Matrix n n R)
    (h : cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0) :
    a * cj s d - b * cj s c = 1 ∧ c * cj s d = d * cj s c ∧ d * cj s a - c * cj s b = 1 := by
  set M := fromBlocks a b c d with hM
  set J : Matrix (n ⊕ n) (n ⊕ n) R := fromBlocks 0 1 (-1) 0 with hJ
  have hJJ : J * J = -1 := by
    rw [hJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have h1 : (-(J * cj s M * J)) * M = 1 := by
    calc (-(J * cj s M * J)) * M = -(J * (cj s M * J * M)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [h, hJJ, neg_neg]
  have h2 : M * (-(J * cj s M * J)) = 1 := mul_eq_one_comm.mp h1
  have e : M * J * cj s M * J = -1 := by
    rw [Matrix.mul_neg] at h2
    simp only [Matrix.mul_assoc] at h2 ⊢
    exact neg_eq_iff_eq_neg.mp h2
  have h3 : M * J * cj s M = J := by
    calc M * J * cj s M = -(M * J * cj s M * (J * J)) := by rw [hJJ]; simp
      _ = -(M * J * cj s M * J * J) := by simp [Matrix.mul_assoc]
      _ = J := by rw [e]; simp
  rw [hM, hJ, cj_fromBlocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h3
  simp at h3
  obtain ⟨-, k1, k2, k3⟩ := h3
  rw [neg_add_eq_sub] at k1 k2 k3
  refine ⟨k1, sub_eq_zero.mp k3, ?_⟩
  rw [← neg_sub, k2, neg_neg]

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

theorem local_choice (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ AlgHom.id F E)
    (hfr : Module.finrank F E = 2) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (a b c d : Matrix n n (Fv F v ⊗[F] E))
    (ha : ∀ i j, a i j ∈ intLoc F E v) (hb : ∀ i j, b i j ∈ intLoc F E v) (hc : ∀ i j, c i j ∈ intLoc F E v)
    (hd : ∀ i j, d i j ∈ intLoc F E v)
    (hu : cj (sigR (Fv F v) σ) (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d =
      fromBlocks 0 1 (-1) 0) :
    ∃ x : Matrix n n (Fv F v ⊗[F] E), (∀ i j, x i j ∈ intLoc F E v) ∧ cj (sigR (Fv F v) σ) x = x ∧
      ∃ z ∈ intLoc F E v, (d + c * x).det * z = 1 := by
  have hinv : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p q => simp [sigR, hσ]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
  set s := sR v σ with hs
  have hss : ∀ y, s (s y) = y := by
    intro y
    apply Subtype.ext
    rw [hs, coe_sR, coe_sR, hinv]
  have hπ : ∀ y, (intLoc F E v).subtype (s y) = sigR (Fv F v) σ ((intLoc F E v).subtype y) := by
    intro y
    exact coe_sR v σ y
  let a' : Matrix n n (intLoc F E v) := fun i j => ⟨a i j, ha i j⟩
  let b' : Matrix n n (intLoc F E v) := fun i j => ⟨b i j, hb i j⟩
  let c' : Matrix n n (intLoc F E v) := fun i j => ⟨c i j, hc i j⟩
  let d' : Matrix n n (intLoc F E v) := fun i j => ⟨d i j, hd i j⟩
  have ea : a'.map (intLoc F E v).subtype = a := rfl
  have eb : b'.map (intLoc F E v).subtype = b := rfl
  have ec : c'.map (intLoc F E v).subtype = c := rfl
  have ed : d'.map (intLoc F E v).subtype = d := rfl
  have h1m : (1 : Matrix n n (intLoc F E v)).map (intLoc F E v).subtype = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hJm : (fromBlocks 0 1 (-1) 0 : Matrix (n ⊕ n) (n ⊕ n) (intLoc F E v)).map (intLoc F E v).subtype
      = fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.fromBlocks_map, Matrix.map_neg _ (map_neg (intLoc F E v).subtype), h1m]
    simp
  have hu' : cj s (fromBlocks a' b' c' d') * fromBlocks 0 1 (-1) 0 * fromBlocks a' b' c' d' =
      fromBlocks 0 1 (-1) 0 := by
    apply Matrix.map_injective Subtype.val_injective
    have key := hu
    rw [← ea, ← eb, ← ec, ← ed, ← Matrix.fromBlocks_map, ← map_cj s _ _ hπ, ← hJm,
      ← Matrix.map_mul, ← Matrix.map_mul] at key
    exact key
  obtain ⟨k1, k2, k3⟩ := unit_rel s a' b' c' d' hu'
  obtain ⟨𝔭, h𝔭, hloc⟩ := exists_max v σ hσ1 hfr
  obtain ⟨B, hB, hdet⟩ := core s hss 𝔭 (isUnit_two v h2) hloc a' b' c' d' k1 k2 k3
  obtain ⟨w, hw⟩ := hdet.exists_right_inv
  refine ⟨B.map (intLoc F E v).subtype, fun i j => (B i j).2, ?_, w, w.2, ?_⟩
  · rw [← map_cj s _ _ hπ, hB]
  · have hm : (d' + c' * B).map (intLoc F E v).subtype = d + c * B.map (intLoc F E v).subtype := by
      rw [Matrix.map_add _ (map_add (intLoc F E v).subtype), Matrix.map_mul, ec, ed]
    rw [← hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using congrArg Subtype.val hw

end Local

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEv
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7}

theorem gen_good {θ : InfFam D} {a b : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e →
      Good S e (fun x : Mx D a b => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) := by
  obtain ⟨S₀, hS₀⟩ := fin_good g hg
  refine ⟨S₀, fun S hS e he x => ?_⟩
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hi1, hi2⟩ := isIdem_eS S
  have heS : e = eS S := ae_ext e (eS S) (fun w => (he1 w).trans (hi1 w).symm)
    (fun v => (he2 v).trans (hi2 v).symm)
  subst heS
  have hinf : ∀ τ (i : Fin a) (j : Fin b), compAt θ τ (eS S • x) i j = compAt θ τ x i j := by
    intro τ i j
    show θ τ (infPart D ((eS S • x) i j)) = θ τ (infPart D (x i j))
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, infPart_eS, one_mul]
  have hfin : (fun (i : Fin a) (j : Fin b) => finPart D ((eS S • x) i j)) =
      sPart S (fun i j => finPart D (x i j)) := by
    funext i j
    show finPart D ((eS S • x) i j) = algebraMap _ _ (indS S) * finPart D (x i j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, finPart_eS]
  simp only [hinf]
  rw [hfin, hS₀ S hS (fun i j => finPart D (x i j))]
  by_cases h : IntOff S x
  · have h' : ∀ v ∉ S, ∀ (i : Fin a) (j : Fin b),
        projV v (fun i j => finPart D (x i j)) i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
      fun v hv i j => by
        have := h v hv i j
        rw [cv_eq] at this
        exact this
    rw [if_pos h', if_pos h]
  · have h' : ¬ ∀ v ∉ S, ∀ (i : Fin a) (j : Fin b),
        projV v (fun i j => finPart D (x i j)) i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
      fun h'' => h (fun v hv i j => by
        have := h'' v hv i j
        rw [cv_eq]
        exact this)
    rw [if_neg h', if_neg h, mul_zero]

end PositivityTheory.Rg.Rsw.L.LGoodEv

namespace PositivityTheory.Rg.Rsw.L

theorem goodEv : IdemEx → GoodEv := by
  intro _ D θ _ a b Φ hΦ
  refine LGoodEv.ev_span _ rfl ?_ Φ hΦ
  rintro φ ⟨f, g, hg, rfl⟩
  exact LGoodEv.gen_good f g hg

end PositivityTheory.Rg.Rsw.L

end
end

