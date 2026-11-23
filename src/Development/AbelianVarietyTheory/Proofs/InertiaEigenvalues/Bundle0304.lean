module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0174
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0281

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegerCoboundaryAdditiveModPrimePow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem int_dvd_of_eq_pow_mul {R : Type} [CommRing R] [IsDomain R] {p : ℕ} (hp : p.Prime)
    (hu : ¬ IsUnit (p : R)) (h0 : (p : R) ≠ 0) :
    ∀ (r : ℕ) (m : ℤ) (w : R), (m : R) = (p : R) ^ r * w → (p : ℤ) ^ r ∣ m := by
  intro r
  induction r with
  | zero => intro m w _; simp
  | succ r ih =>
    intro m w hm
    have hpm : (p : ℤ) ∣ m := by
      by_contra hnd
      have hcop : IsCoprime (p : ℤ) m :=
        (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hnd
      obtain ⟨u, v, huv⟩ := hcop
      apply hu
      have h1 : ((u * p + v * m : ℤ) : R) = 1 := by rw [huv]; simp
      push_cast at h1
      rw [hm] at h1
      refine isUnit_iff_exists_inv.mpr ⟨u + v * (p : R) ^ r * w, ?_⟩
      rw [← h1]; ring
    obtain ⟨m', rfl⟩ := hpm
    have hm' : (m' : R) = (p : R) ^ r * w := by
      push_cast at hm
      apply mul_left_cancel₀ h0
      rw [hm]; ring
    rw [pow_succ, mul_comm ((p : ℤ) ^ r)]
    exact mul_dvd_mul_left _ (ih m' w hm')

theorem coboundary_int_additive_mod : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A : Subgroup (L ≃ₐ[K] L)) (x : L) (a : (L ≃ₐ[K] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → ∀ σ ∈ A, ∀ τ ∈ A, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A x a hp hE hord hx σ hσ τ hτ
  obtain ⟨zσ, hzσ, eσ⟩ := hx σ hσ
  obtain ⟨zτ, hzτ, eτ⟩ := hx τ hτ
  obtain ⟨zστ, hzστ, eστ⟩ := hx (σ * τ) (A.mul_mem hσ hτ)
  have hσz : σ zτ ∈ 𝒪[L] := by
    have := (integerAlgEquiv K L σ ⟨zτ, hzτ⟩).2
    simpa using this
  let w : 𝒪[L] := ⟨σ zτ + zσ - zστ, Subring.sub_mem _ (Subring.add_mem _ hσz hzσ) hzστ⟩
  have hmul : (σ * τ) x - x = σ (τ x - x) + (σ x - x) := by
    rw [AlgEquiv.mul_apply, map_sub]; ring
  have hστ : σ (τ x - x) = (a τ : L) + (p : L) ^ r * σ zτ := by
    rw [eτ, map_add (f := _), map_mul, map_pow, map_intCast, map_natCast]
  have key : (((a (σ * τ) - a σ - a τ : ℤ)) : 𝒪[L]) = (p : 𝒪[L]) ^ r * w := by
    apply Subtype.ext
    simp only [w, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, Subring.coe_intCast]
    push_cast
    rw [hmul, hστ, eσ] at eστ
    linear_combination -eστ
  have hu : ¬ IsUnit (p : 𝒪[L]) := by
    rintro ⟨u, hu⟩
    have h := IsDiscreteValuationRing.addVal_eq_zero_of_unit (R := 𝒪[L]) u
    unfold OrdIs at hord
    rw [hu, hord] at h
    have : E = 0 := by exact_mod_cast h
    omega
  have h0 : (p : 𝒪[L]) ≠ 0 := by
    intro h
    unfold OrdIs at hord
    rw [h, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_coe E hord
  exact int_dvd_of_eq_pow_mul hp hu h0 r _ w key

end GlobalTheory.PMon.Ram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormLatticeEqSumLocalisedLattices
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.LatSplit

theorem form_gen_span {L V M ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {σ : L →+* ℂ} (j : V →ₛₗ[σ] M) (b : Module.Basis ι L V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤)
    (T : Finset M) (hT : Submodule.span ℂ (T : Set M) = ⊤) (hsub : ∀ x ∈ T, x ∈ Set.range j) :
    {x | j x ∈ T}.Finite ∧ Submodule.span L {x | j x ∈ T} = ⊤ := by
  haveI : Finite ι := hb.1.finite
  haveI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hB : ∀ i, B i = j (b i) := fun i => by simp [B]
  have key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x) := fun l => by
    refine ⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]
  have hinj : Function.Injective j := fun x y hxy => by
    refine b.ext_elem fun i => σ.injective ?_
    obtain ⟨l', hl'⟩ := key (b.coord i)
    have h1 := hl' x
    rw [hxy, hl' y] at h1
    exact h1.symm
  refine ⟨T.finite_toSet.preimage hinj.injOn, ?_⟩
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨l', hl'⟩ := key l
  have h1 : l' = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hsub y hy
    have hx : l x = 0 := hl (Submodule.subset_span hy)
    show l' (j x) = 0
    rw [hl', hx, map_zero]
  refine hl0 (LinearMap.ext fun x => σ.injective ?_)
  rw [← hl', h1]
  simp

variable {D : D7} {M : MtFam D}

theorem genSet_props (j : ℕ) (w : D.what₂.places.Pl) :
    (genSet D (D.what₂.muTw w) j).Finite ∧ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j) = ⊤ :=
  form_gen_span (D.what₂.jMt _ j) (Module.Free.chooseBasis _ _) (D.what₂.jMt_basis _ j _) _
    (D.what₂.MtLat _ j).span_top (D.what₂.MtLat_sub _ j)

theorem latLoc_fg (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : (latLoc B j w).FG :=
  Submodule.fg_span ((genSet_props (D := D) j w).1.image _)

theorem latLoc_span (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Submodule.span (FractionRing (B.Oc j w)) (latLoc B j w : Set (B.V j w)) = ⊤ := by
  rw [latLoc, Submodule.span_span_of_tower]
  have hG := (genSet_props (D := D) j w).2
  have key : ∀ x ∈ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j),
      B.iV j w x ∈ Submodule.span (FractionRing (B.Oc j w)) (B.iV j w '' genSet D (D.what₂.muTw w) j) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  rw [eq_top_iff, ← (B.iV_basis j w b).2, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact key _ (hG ▸ Submodule.mem_top)

theorem alg_stable (B : NLocBase D M) {j : ℕ} {w : D.what₂.places.Pl} (hl : LatStable B j w) :
    ∀ t ∈ heckeAlg B j w, ∀ x ∈ latLoc B j w, t x ∈ latLoc B j w := by
  intro t ht
  induction ht using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    exact hl v k hvk
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact (latLoc B j w).smul_mem r hx
  | add f g _ _ hf hg => intro x hx; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  | mul f g _ _ hf hg => intro x hx; exact hf _ (hg x hx)

end GlobalTheory.LatSplit

namespace GlobalTheory.LatSplit

variable {D : D7} {M : MtFam D}

theorem proj_facts {K V : Type} [Field K] [AddCommGroup V] [Module K V] {P Q : Submodule K V} (hc : IsCompl P Q)
    (t : Module.End K V) (hP : ∀ x ∈ P, t x = x) (hQ : ∀ x ∈ Q, t x = 0) (y : V) : t y ∈ P ∧ y - t y ∈ Q := by
  have hy : y ∈ P ⊔ Q := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add (f := _), hP p hp, hQ q hq, add_zero, add_sub_cancel_left]
  exact ⟨hp, hq⟩

theorem part_le_off {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [IsLocalRing O] (T : Subalgebra O (Module.End K V)) {I J : Ideal T} (h : I ≠ J) :
    NCov.part T I ≤ NCov.off T J :=
  iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ J) => NCov.W T (NCov.pt ψ)) ψ
    (by rw [hψ]; exact h) le_rfl

theorem exists_proj (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (hl : LatStable T.B j w) (I : Ideal (heckeAlg T.B j w)) :
    ∃ t ∈ heckeAlg T.B j w, (∀ x ∈ NCov.part (heckeAlg T.B j w) I, t x = x) ∧
      ∀ x ∈ NCov.off (heckeAlg T.B j w) I, t x = 0 := by
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  exact _root_.GlobalTheory.part_projector_mem_adjoin (T.B.Oc j w) (FractionRing (T.B.Oc j w)) (T.B.V j w) (heckeGens T.B j w) hS hsplit hint
    (latLoc T.B j w) (latLoc_fg T.B j w) (latLoc_span T.B j w)
    (fun a ha x hx => alg_stable T.B hl a (Algebra.subset_adjoin ha) x hx) I

theorem main : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m →
    D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ∀ y : T.B.V j w,
    y ∈ latLoc T.B j w ↔ ∃ z : ∀ i : D.nd.Loc, TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i),
      (∀ i, z i ∈ D.nd.MtIn i) ∧ y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (z i.1) := by
  classical
  intro D M T j w h1 h2 hw hstd hl y
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  choose tp htp hpart hoff using exists_proj T hstd h1 h2 hw hl
  have hc := fun I => NCov.isCompl_part_off hinj hS hsplit hint I
  have eL : latC T.B j w = latLoc T.B j w := rfl

  have hlp : ∀ I x, x ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) I → x ∈ latLoc T.B j w := by
    intro I x hx
    obtain ⟨hxP, hxL⟩ := Submodule.mem_inf.1 hx
    obtain ⟨l, hlL, q, hq, rfl⟩ := Submodule.mem_sup.1 hxL
    have e : tp I (l + q) = l + q := hpart I _ hxP
    rw [map_add (f := _), hoff I q hq, add_zero] at e
    rw [← e]
    exact alg_stable T.B hl _ (htp I) l hlL
  constructor
  · intro hy

    have ex : ∀ i (h : i ∈ D.nd.locs j w), ∃ z, z ∈ D.nd.MtIn i ∧ T.Psi j w i h z = tp (T.mx j w i) y := by
      intro i h
      haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
      have hm : tp (T.mx j w i) y ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) (T.mx j w i) := by
        refine Submodule.mem_inf.2 ⟨(proj_facts (hc _) _ (hpart _) (hoff _) y).1, ?_⟩
        exact Submodule.mem_sup_left (alg_stable T.B hl _ (htp _) y hy)
      rw [← map_psiO_MtIn T hstd h] at hm
      obtain ⟨z, hz, e⟩ := Submodule.mem_map.1 hm
      exact ⟨z, hz, e⟩
    refine ⟨fun i => if h : i ∈ D.nd.locs j w then (ex i h).choose else 0, fun i => ?_, ?_⟩
    · by_cases h : i ∈ D.nd.locs j w
      · dsimp only; rw [dite_eq_left h]; exact (ex i h).choose_spec.1
      · dsimp only; rw [dite_eq_right h]; exact Submodule.zero_mem _
    · have hsum : ∑ i ∈ (D.nd.locs j w).attach,
          T.Psi j w i.1 i.2 (if h : i.1 ∈ D.nd.locs j w then (ex i.1 h).choose else 0) =
          ∑ i ∈ (D.nd.locs j w).attach, tp (T.mx j w i.1) y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dite_eq_left i.2]
        exact (ex i.1 i.2).choose_spec.2
      rw [hsum, ← sub_eq_zero]
      refine NCov.eq_zero_of_forall_mem_off hinj hS hsplit hint ((D.nd.locs j w).image (T.mx j w))
        (fun I hI => ?_) ?_
      · obtain ⟨i, hi, rfl⟩ := T.mx_all j w h1 h2 hw I hI
        exact Finset.mem_image_of_mem _ hi
      · intro I hI
        obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.1 hI
        rw [← Finset.add_sum_erase _ _ (Finset.mem_attach _ ⟨i0, hi0⟩), sub_add_eq_sub_sub]
        refine Submodule.sub_mem _ (proj_facts (hc _) _ (hpart _) (hoff _) y).2 (Submodule.sum_mem _ fun i hi => ?_)
        have hne : T.mx j w i.1 ≠ T.mx j w i0 := by
          intro e
          have := T.mx_inj j w i.2 hi0 e
          exact (Finset.mem_erase.1 hi).1 (Subtype.ext this)
        exact part_le_off _ hne (proj_facts (hc _) _ (hpart _) (hoff _) y).1
  · rintro ⟨z, hz, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
    refine hlp (T.mx j w i.1) _ ?_
    rw [← map_psiO_MtIn T hstd i.2]
    exact Submodule.mem_map_of_mem (hz i.1)

end GlobalTheory.LatSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem fil_mul_entries {n : Type} [Fintype n] {A B : Matrix n n P.R.BdR}
    (hA : ∀ i j, A i j ∈ Fil P 0) (hB : ∀ i j, B i j ∈ Fil P 0) : ∀ i j, (A * B) i j ∈ Fil P 0 :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Fil_sum fun k _ => Fil_mul_left (hA i k) (hB k j)

theorem fil_blockDiagonal_entries {r : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (V : Fin r → Matrix n n P.R.BdR) (h : ∀ m i j, V m i j ∈ Fil P 0) :
    ∀ a b, Matrix.blockDiagonal V a b ∈ Fil P 0 := fun a b => by
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact h _ _ _
  · exact Fil_zero_mem 0

theorem fil_kd_entries {m : Type} [Fintype m] [DecidableEq m] (g : GL m ↥(MaximalUnramifiedExtension l)) :
    ∀ a b, ((Units.map ((kd P).mapMatrix : Matrix m m ↥(MaximalUnramifiedExtension l) →+* Matrix m m P.R.BdR).toMonoidHom g :
      GL m P.R.BdR) : Matrix m m P.R.BdR) a b ∈ Fil P 0 := fun a b => by
  rw [Units.coe_map]
  exact kd_mem_Fil P _

theorem unitM_U0_of_unitM : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR),
    (∀ m, UnitM P (U m)) → UnitM P (U0 P ω hdet U) := by
  intro l _ P r ω hdet n _ _ U hU
  constructor
  · unfold U0
    rw [Units.val_mul, ← map_inv]
    exact fil_mul_entries (fil_kd_entries _)
      (fil_blockDiagonal_entries _ fun m i j => (hU m).1 i j)
  · unfold U0
    rw [mul_inv_rev, inv_inv, Units.val_mul]
    exact fil_mul_entries
      (fil_blockDiagonal_entries _ fun m i j => (hU m).2 i j) (fil_kd_entries _)

end GlobalTheory.PMon.ResR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JDANEqRange
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.NL.WkRange

theorem jD_smul_letter {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
    {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (T : Lt K LL) (a : AA K LL) (x : W.DD T) :
    E.tie.jD T (a • x) = inclR LL (E.tie.io a) • E.tie.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.tie.jD_smul, E.tie.ioE_ext]

theorem jD_aN_eq_range : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL), ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T letπ : Set (W.DD T)) = Set.range fun a : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (a i)) • y i := by
  intro l _ P AI K s LL h W E T
  obtain ⟨S, hS⟩ := W.N_fg T
  let n : Fin S.card → W.DD T := fun i => (S.equivFin.symm i : W.DD T)
  have hrange : Set.range n = (S : Set (W.DD T)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2
    · intro hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩
  have hspan : W.N T = Submodule.span (AA K LL) (Set.range n) := by rw [hrange, hS]
  refine ⟨S.card, fun i => E.tie.jD T ((letπ : AA K LL) • n i), ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    rw [hspan] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm
    refine ⟨c, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [jD_smul_letter]
    exact smul_comm _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨∑ i, c i • ((letπ : AA K LL) • n i), ?_, ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩
      · rw [hspan]
        exact (Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩
      · simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum]
      exact Finset.sum_congr rfl fun i _ => jD_smul_letter E T _ _

end GlobalTheory.NL.WkRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsOverLettersOfCrysWith
section
noncomputable section

open GlobalTheory.WachUse GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing

namespace GlobalTheory.WachUse.HeightsProof

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem letφ_letE (i : ZMod n) : letφ W.φ₀ (letE (i - 1) : LetA O n) = letE i := by
  funext j
  change W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · have hj' : j - 1 ≠ i - 1 := fun h => hj (sub_left_injective h)
    simp [letE, hj, hj']

theorem φD_letE (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE (letE (i - 1))) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul, letφ_letE] at this

theorem Nl_le (T : LocLat G Qp LL O) (i : ZMod n) : W.Nl T i ≤ W.N T := by
  rintro _ ⟨x, hx, rfl⟩
  exact (W.N T).smul_mem _ hx

theorem of_heightBounds (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hb : HeightBounds W T M h) (i : ZMod n) :
    (∀ x ∈ W.N T, W.Q ^ M i • (letE i : LetA O n) • W.φD T x ∈ W.N T) ∧
      ∀ y ∈ W.N T, W.Q ^ h i • (letE i : LetA O n) • y ∈ W.φpull T := by
  refine ⟨fun x hx => Nl_le W T i ((hb i).1 _ ?_), fun y hy => ?_⟩
  · rw [← φD_letE]
    exact Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (Nl_le W T (i - 1))) ((hb i).2 _ ⟨y, hy, rfl⟩)

theorem jumpsOverLetters_of_crysWith (T : LocLat G Qp LL O) [FiniteDimensional LL ↥(DdR PD T.ρ)]
    (U : ZMod n → Multiset ℤ) (M h : ZMod n → ℕ) (hU : CrysWith PD W.emb T.ρ U)
    (hb : ∀ i, ∀ u ∈ U i, -(M i : ℤ) ≤ u ∧ u ≤ h i) : JumpsOverLetters W T M h := by
  intro i τ hτ a ha
  have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite PD T.ρ τ a).2.2.1 ha
  rw [hU.2 i τ hτ a] at h1
  exact hb i a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))

end Generic

theorem heights_of_finite {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} {C : LocCmpT l P AI H E} (hJ : HeightsFromJumps l P AI H E C)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (hfin : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) T.ρ)) :
    Heights (H.W K s LL h) := by
  intro T U M hh hU hb
  haveI := hfin T
  exact of_heightBounds _ T M hh
    (hJ K s LL h T hU.1 M hh (jumpsOverLetters_of_crysWith _ T U M hh hU hb)).1

theorem heights_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (C : LocCmpT l P AI H E), Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H E C → ∀ (K LL : FinExt l) (h : CaseA K LL), Heights (H.W K 1 LL h.2.2) := by
  rintro l _ P AI H E C ⟨Ti⟩ hJ K LL h
  exact heights_of_finite hJ K 1 LL h.2.2 fun T => (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI Ti K LL T.V T.ρ).1

end GlobalTheory.WachUse.HeightsProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesAboveEllInCutUnitDelta
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.LocalCocycleConstruction

open GlobalTheory.Cut.LocCoc

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  intro D i r ρ π Xs S _ hG _ w hw
  obtain ⟨-, hdec, hψ, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩ := hG
  have key : ∀ γ u, (((S.ψρ fun x' => rTwO D.nd i r (S.p x') γ).map (toK D.nd i)).mulVec (S.e u).1,
      fun c : Fin D.R.t => toK D.nd i (S.ψχ c fun x' => rTwO D.nd i r (S.p x') γ) * (S.e u).2 c) =
      toK D.nd i (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) γ).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) γ : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) := by
    intro γ u
    rw [← hψ _ (GlobalTheory.Cut.LocCoc.inR'_tw i r S γ) u, ← hdec, ← map_smul, hπ, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [mapM, rTwO, twistM]
  refine ⟨fun f hf => GlobalTheory.Cut.LocCoc.inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf,
    fun c f hf => GlobalTheory.Cut.LocCoc.inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf⟩
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.1 p) (key γ (S.e.symm (Pi.single q 1, 0)))
    simpa [mapM, WpO, twistM] using h
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.2 c) (key γ (S.e.symm (0, Pi.single c 1)))
    obtain rfl : p = q := Subsingleton.elim _ _
    simpa [chiRatO, twistM, mul_comm] using h

end GlobalTheory.Cut.LocalCocycleConstruction
end

