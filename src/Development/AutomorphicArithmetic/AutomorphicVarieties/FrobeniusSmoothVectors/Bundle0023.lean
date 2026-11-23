module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Mathlib.RingTheory.Filtration
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVring
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem alg_vring {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (hi : Function.Injective (algebraMap C K))
    (hn : IsNoetherianRing (lauSub P)) : IsVertexRing C (vertex h) := by
  have hcoeff : ∀ c : C, ((algebraMap C (lauSub P) c : lauSub P) : AddMonoidAlgebra K ℤ).coeff 0 = algebraMap C K c := by
    intro c
    simp
  refine ⟨hn, ?_, alg_sep h hn, ?_, ?_⟩
  · intro c c' hcc
    apply hi
    rw [← hcoeff c, ← hcoeff c', hcc]
  · ext c
    rw [Ideal.mem_comap, mem_vertex, hcoeff]
    constructor
    · rintro ⟨c', hc', he⟩
      rwa [← hi he]
    · intro hc
      exact ⟨c, hc, rfl⟩
  · intro d
    obtain ⟨c, hc⟩ := h.zero _ (d.2 0)
    refine ⟨c, ?_⟩
    rw [mem_vertex]
    refine ⟨0, (maximalIdeal C).zero_mem, ?_⟩
    simp [hc]

private theorem alg_ev (C K : Type) [CommRing C] [CommRing K] [Algebra C K] :
    ∃ e : AddMonoidAlgebra K ℤ →ₐ[C] K, ∀ j x, e (AddMonoidAlgebra.single j x) = x := by
  refine ⟨AddMonoidAlgebra.liftNCAlgHom (AlgHom.id C K) 1 (fun _ _ => Commute.one_right _), fun j x => ?_⟩
  exact (AddMonoidAlgebra.liftNC_single _ _ _ _).trans (by simp)

theorem UpperTheory.V.Fr.alg :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra O K] [Algebra C K] [IsScalarTower O C K], Function.Injective (algebraMap C K) → ∀ ρ : NRep F n K, Cone O C ρ → ∃ (ξ : S.A →ₐ[O] K) (β : S.B →ₐ[O] C), S.u.map (ξ : S.A →+* K) = ρ ∧ ∀ b, ξ (S.inc b) = algebraMap C K (β b) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ K _ _ _ _ hi ρ hcone
  have hv := alg_vertex C ρ hcone
  haveI := alg_ft C ρ hcone.fg
  have hN : IsNoetherianRing (lauSub (NRep.part C ρ)) := Algebra.FiniteType.isNoetherianRing C _
  have hvr := alg_vring hv hi hN
  obtain ⟨ρD, h1, h2⟩ := alg_lau C ρ hcone
  have hmod := alg_model C ρ hcone hv ρD h1 h2
  letI : Algebra O (lauSub (NRep.part C ρ)) :=
    ((algebraMap C (lauSub (NRep.part C ρ))).comp (algebraMap O C)).toAlgebra
  haveI : IsScalarTower O C (lauSub (NRep.part C ρ)) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ξ, β, hξ, hβ⟩ := alg_limit S C (vertex hv) ρD hvr hmod
  obtain ⟨e, he⟩ := alg_ev C K
  let ev : lauSub (NRep.part C ρ) →ₐ[O] K := (e.comp (lauSub (NRep.part C ρ)).val).restrictScalars O
  refine ⟨ev.comp ξ, β, ?_, fun b => ?_⟩
  · apply NRep.ext
    · ext g i j
      rw [NRep.map_r]
      have hr := NRep.map_r (ξ : S.A →+* lauSub (NRep.part C ρ)) S.u g i j
      rw [hξ] at hr
      show e ((ξ (S.u.r g i j) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
      have hr' : ξ (S.u.r g i j) = ρD.r g i j := hr.symm
      rw [hr', h1, he]
    · funext v i
      ext g
      rw [NRep.map_ψ]
      have hp := NRep.map_ψ (ξ : S.A →+* lauSub (NRep.part C ρ)) S.u v i g
      rw [hξ] at hp
      show e ((ξ ((S.u.ψ v i g : S.Aˣ) : S.A) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
      have hp' : ξ ((S.u.ψ v i g : S.Aˣ) : S.A) = ((ρD.ψ v i g : (lauSub (NRep.part C ρ))ˣ) : lauSub (NRep.part C ρ)) := hp.symm
      rw [hp', h2, he]
  · show e ((ξ (S.inc b) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
    rw [hβ b]
    exact e.commutes (β b)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ArtinRees
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem artin_rees {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (P Q : Submodule R M) (hQ : Q.FG) (N : ℕ) : ∃ K : ℕ, ∀ x ∈ P, x ∈ I ^ K • Q → x ∈ I ^ N • P := by
  haveI : Module.Finite R Q := Module.Finite.iff_fg.mpr hQ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (P.comap Q.subtype)
  refine ⟨k + N, fun x hxP hxQ => ?_⟩
  have hmap : I ^ (k + N) • Q = (I ^ (k + N) • (⊤ : Submodule R Q)).map Q.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [hmap] at hxQ
  obtain ⟨y, hy, rfl⟩ := hxQ
  have hy' : y ∈ I ^ (k + N) • ⊤ ⊓ P.comap Q.subtype := ⟨hy, hxP⟩
  rw [hk _ (Nat.le_add_right k N), Nat.add_sub_cancel_left] at hy'
  have h2 : I ^ N • (I ^ k • ⊤ ⊓ P.comap Q.subtype) ≤ I ^ N • P.comap Q.subtype :=
    Submodule.smul_mono le_rfl inf_le_right
  have h3 := Submodule.mem_map_of_mem (f := Q.subtype) (h2 hy')
  rw [Submodule.map_smul''] at h3
  exact Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _) h3

private theorem val_prod {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {F : UpperTheory.V.Fr.Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (L : List (F.G0 × Fin n × Fin n)) :
    (((L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod : S.A) : S.R) = (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih, List.map_cons, List.prod_cons]
    rfl

theorem UpperTheory.V.Fr.cone_u :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ [IsCO O S.B], Cone O S.B S.u ∧ Integral O S.B S.u := by
  intro l _ O _ _ _ _ F C₀ n hF hn S _
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨hgrI, hgrM, hgr0, hgrFG, hfin, hnoethA, hmem⟩ := gr_A hF hn S
  obtain ⟨hcx, haB, hψB, hAR⟩ := cont_u hF hn S
  have hres : ∀ x : S.B, res O S.B x = res O S.R (x : S.R) := fun x => (res_map S.B.val x).symm
  have hmax : maximalIdeal S.B = S.mB := by
    ext x
    rw [← res_eq_zero_iff O S.B x, hres, res_eq_zero_iff]
    rfl
  have hdiag : ∀ g i, res O S.R (S.ρ.r g i i) = ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun g i => S.lift.2.1.1 g i
  have hpsi : ∀ v i g, res O S.R ((S.ρ.ψ v i g : S.Rˣ) : S.R) =
      ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun v i g => S.lift.2.1.2 v i g
  have hoff : ∀ g (i j : Fin n), i ≠ j → res O S.R (S.ρ.r g i j) = 0 :=
    fun g i j h => S.lift.2.2 g i j h
  have hA : ∀ g i, algebraMap S.B S.A (S.aB g i) = S.u.r g i i := fun _ _ => rfl
  have hPsi : ∃ χ, IsPsi O F n χ ∧ ∀ v i g, algebraMap S.B S.A (χ v i g) = ((S.u.ψ v i g : S.Aˣ) : S.A) := by
    refine ⟨S.ψB, fun v i => ⟨?_, fun g => ?_⟩, fun v i g => rfl⟩
    · rw [hmax]; exact hψB v i
    · rw [hres]; exact hpsi v i g
  refine ⟨⟨fun g i => ⟨S.aB g i, rfl, by rw [hres]; exact hdiag g i⟩, ?_, ?_, ?_, hPsi⟩, ⟨?_, hPsi, ?_⟩⟩
  · intro L hL ⟨s, hs, hne⟩
    have hm : (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod ∈ S.B := S.mon_mem ⟨L, hL, rfl⟩
    refine ⟨⟨_, hm⟩, ?_, Subtype.ext (val_prod S L).symm⟩
    rw [← res_eq_zero_iff O S.B, hres]
    show res O S.R (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod = 0
    rw [map_list_prod, List.map_map]
    apply List.prod_eq_zero
    exact List.mem_map.2 ⟨s, hs, hoff _ _ _ hne⟩
  · intro i j
    haveI := isNoetherian_of_fg_of_noetherian _ (hgrFG (w n i - w n j))
    have hle : Submodule.span S.B (Set.range fun g => S.u.r g i j) ≤ S.gr (w n i - w n j) :=
      Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hmem g i j)
    haveI := isNoetherian_of_le hle
    exact Module.Finite.iff_fg.1 inferInstance
  · intro i j N
    rw [hmax]
    obtain ⟨K, hK⟩ := artin_rees S.mB (Submodule.span S.B (Set.range fun g => S.u.r g i j))
      (S.gr (w n i - w n j)) (hgrFG _) N
    obtain ⟨M, hM⟩ := hAR (w n i - w n j) K
    have hc := S.lift.1.1 i j M
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro g
    filter_upwards [hc g] with g' hg'
    rw [Ideal.Quotient.eq] at hg'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    apply hK
    · exact Submodule.sub_mem _ (Submodule.subset_span ⟨g', rfl⟩) (Submodule.subset_span ⟨g, rfl⟩)
    · apply hM _ (Submodule.sub_mem _ (hmem g' i j) (hmem g i j))
      exact hg'
  · refine ⟨S.trB, ⟨?_, fun g => ?_⟩, fun g => ?_⟩
    · rw [hmax]
      intro N
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have h2 := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (haB i N) g
      filter_upwards [h2] with g' hg'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Space.trB, map_sum, hg']
    · show res O S.B (∑ i, S.aB g i) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hres]; exact hdiag g i
    · show algebraMap S.B S.A (∑ i, S.aB g i) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Matrix.trace]
      rfl
  · obtain ⟨-, -, -, -, hst⟩ := UpperTheory.V.Fr.star hF
    have hz : ∀ i : Fin n, (S.u.r F.g0 - S.u.r (F.star F.g0)) i i = S.u.r F.g0 i i - S.u.r F.g0 i.rev i.rev :=
      fun i => by rw [Matrix.sub_apply, hst]
    rcases hn with rfl | rfl
    · refine ⟨S.aB F.g0 0 - S.aB F.g0 1, ?_, fun i => ?_⟩
      · rw [map_sub, hres, hres]
        erw [hdiag, hdiag]
        simp [w]
      · rw [hz, map_sub, hA, hA]
        fin_cases i <;> simp [w] <;> ring
    · refine ⟨S.aB F.g0 0 - S.aB F.g0 2, ?_, fun i => ?_⟩
      · rw [map_sub, hres, hres]
        erw [hdiag, hdiag]
        simp [w]
      · rw [hz, map_sub, hA, hA]
        fin_cases i <;> simp [w] <;> ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGbox
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_bt {K : Type} [CommRing K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K} :
    UpT A ↔ A.BlockTriangular id := ⟨fun h i j e => h i j e, fun h _ _ e => h e⟩

private theorem upT_mul' {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) := upT_bt.2 ((upT_bt.1 hA).mul (upT_bt.1 hB))

private theorem upT_inv {K : Type} [CommRing K] {n : ℕ} {u : GL (Fin n) K} (h : UpT (u : Matrix (Fin n) (Fin n) K)) :
    UpT ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  letI := u.invertible
  rw [Matrix.coe_units_inv]
  exact upT_bt.2 (Matrix.blockTriangular_inv_of_blockTriangular (upT_bt.1 h))

private theorem upT_diag {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B)
    (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with e | e
    · rw [hA i b e, zero_mul]
    · rw [hB b i e, mul_zero]
  · simp

private theorem conj_assoc {K : Type} [CommRing K] {n : ℕ} (u g : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    ((u * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (((u * g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (u : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) * M *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

private theorem conj_diag {K : Type} [CommRing K] {n : ℕ} {u : GL (Fin n) K} (h : UpT (u : Matrix (Fin n) (Fin n) K))
    {T : Matrix (Fin n) (Fin n) K} (hT : UpT T) (i : Fin n) :
    ((u : Matrix (Fin n) (Fin n) K) * T * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = T i i := by
  have e := upT_diag h (upT_inv h) i
  rw [Units.mul_inv, Matrix.one_apply_eq] at e
  rw [upT_diag (upT_mul' h hT) (upT_inv h), upT_diag h hT, mul_right_comm, ← e, one_mul]

theorem UpperTheory.V.Fr.ep_gbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → F.del F.c = -1 → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (ρ : NRep F 3 R) (B₀ : Box F 3 R), B₀.Of ρ → (ρ.bar O).Good → (∀ g a b, ρ.r g a b ∈ evp σ (pw a b)) → (∀ v i s, (ρ.ψ v i s : R) ∈ evp σ 0) → ∃ (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), B.Of ρ ∧ B.r = B₀.r ∧ B.Gr σ π := by
  intro l _ k _ F O _ _ _ _ h2 hc R _ _ _ σ hσ ρ B₀ hB hG hr hψ
  have hr' : ∀ g, GrM σ pq pq (ρ.r g) := fun g a b => pw_eq a b ▸ hr g a b
  have hres : ∀ v s, (B₀.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := fun v s => hB.res (F.loc0 v s)
  have htri : ∀ v s, UpT ((B₀.g v : Matrix (Fin 3) (Fin 3) R) * ρ.r (F.loc0 v s) *
      (((B₀.g v)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) := fun v s => hres v s ▸ B₀.tri v s
  have key : ∀ v, ∃ (u : GL (Fin 3) R) (α : Fin 3 → ZMod 2), UpT (u : Matrix (Fin 3) (Fin 3) R) ∧
      GrM σ α pq ((u * B₀.g v : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := fun v => by
    refine ep_gflag O h2 R σ hσ (fun s => ρ.r (F.loc0 v s)) (B₀.g v) (fun s => hr' _) (htri v)
      (fun s i => by rw [hB.psi]; exact hψ v i s) ?_
    obtain ⟨s, hs⟩ := hG.ψd v
    refine ⟨s, fun i j hij => ?_⟩
    rw [hB.psi, hB.psi]
    by_contra hu
    have hm : (ρ.ψ v i s : R) - ρ.ψ v j s ∈ maximalIdeal R := hu
    rw [← res_eq_zero_iff (O := O), map_sub, sub_eq_zero] at hm
    exact hs i j hij (Units.ext hm)
  choose u π hu hg using key
  refine ⟨⟨B₀.r, B₀.nu, fun v => u v * B₀.g v, fun v s => ?_⟩, π, ⟨hB.atc, hB.res, fun v i s => ?_⟩, rfl,
    fun s => ?_, hg⟩
  · rw [conj_assoc]
    exact upT_mul' (upT_mul' (hu v) (B₀.tri v s)) (upT_inv (hu v))
  · show (((u v * B₀.g v : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * ρ.r (F.loc0 v s) *
      (((u v * B₀.g v)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i = _
    rw [conj_assoc, conj_diag (hu v) (htri v s), hB.psi]
  · show GrM σ pq pq (B₀.r s).mat
    rcases Int.units_eq_one_or (F.del s) with e | e
    · exact hB.res ⟨s, e⟩ ▸ hr' ⟨s, e⟩
    · have hm : s * F.c⁻¹ ∈ F.del.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, e, hc, mul_inv_cancel]
      have h1 : (B₀.r F.c).left = 1 := Units.ext hB.atc
      have h3 : (B₀.r s).mat = (B₀.r (s * F.c⁻¹)).mat := by
        conv_lhs => rw [← inv_mul_cancel_right s F.c, map_mul]
        unfold GG.mat
        rw [SemidirectProduct.mul_left, h1, map_one, mul_one]
      rw [h3]
      exact hB.res ⟨_, hm⟩ ▸ hr' ⟨_, hm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpHasobs
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_hasobs :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (ρ : NRep F 3 R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → B.Gr σ π → ∀ h : (B.bar O).Ev π, ∀ j, HasObsG O σ j (coneH2 F.loc (h.ad j) ((B.bar O).bp j)) := by
  intro l _ k _ _ F C₀ hF O _ _ _ _ h2 R _ _ _ σ hσ ρ B π hU hOf hCont hGood hGr h j
  intro C' _ _ _ p σ' hp hker hσ' hpσ
  obtain ⟨a⟩ := pr_setlift hF O C' R p B hp hker hCont
  obtain ⟨D, hD⟩ := ep_glift O h2 C' R p σ' σ hσ' hpσ B π hGr a
  have hco : ∀ u : ↥(formp σ' (RingHom.ker p) j),
      (∀ x : F.Γ × F.Γ, (D.co u).1 x ∈ adp (ResidueField O) j) ∧
        ∀ (v : F.V) (s : F.Gv v), (D.co u).2 v s ∈ adp (ResidueField O) j :=
    by
      intro u
      have hu' : ∀ i, i ≠ j → ∀ y : RingHom.ker p, (y : C') ∈ evp σ' i → (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) y = 0 := u.2
      have key : ∀ M : Matrix (Fin 3) (Fin 3) C', GrM σ' pq pq M →
          M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O)) ∈ adp (ResidueField O) j := by
        intro M hM
        change ∀ a b, pw a b ≠ j → M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O)) a b = 0
        intro a b hab
        rw [Matrix.map_apply]
        have hmem := hM a b
        rw [← pw_eq] at hmem
        unfold evK
        split_ifs with hk
        · exact hu' (pw a b) hab ⟨M a b, hk⟩ hmem
        · rfl
      obtain ⟨h1, hsub, hmul, hinv, hsgn⟩ := ep_grm σ'
      refine ⟨fun x => ?_, fun v s => ?_⟩
      · refine key (D.om x) ?_
        unfold SetLift.om
        rw [Units.val_mul, Units.val_mul]
        exact hsub _ _ _ _ (hmul _ _ _ _ _ (hmul _ _ _ _ _ (hD.r x.1) (hsgn _ _ (hD.r x.2)))
          (hinv _ _ _ (hD.r (x.1 * x.2)))) (h1 pq)
      · have hX : GrM σ' pq pq ↑((D.g v)⁻¹ * D.t v s * D.g v) := by
          rw [Units.val_mul, Units.val_mul]
          exact hmul _ _ _ _ _ (hmul _ _ _ _ _ (hinv _ _ _ (hD.g v)) (hD.t v s)) (hD.g v)
        refine key (D.a v s) ?_
        unfold SetLift.a
        rw [Units.val_mul]
        exact hsub _ _ _ _ (hmul _ _ _ _ _ (hD.r _) (hinv _ _ _ hX)) (h1 pq)
  have hom := pr_omk hF O C' R p B D hker
  let Ψ : ↥(formp σ' (RingHom.ker p) j) →ₗ[ResidueField O]
      ((F.Γ × F.Γ → ↥(adp (ResidueField O) j)) × ((v : F.V) → F.Gv v → ↥(adp (ResidueField O) j))) :=
    { toFun := fun u => (fun x => ⟨(D.co u).1 x, (hco u).1 x⟩, fun v s => ⟨(D.co u).2 v s, (hco u).2 v s⟩)
      map_add' := by
        intro u w
        refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>
          simp [map_add (f := _)]
      map_smul' := by
        intro c u
        refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>
          simp [map_smul] }
  have hmem : ∀ u, Ψ u ∈ continuousCocycles2 F.loc (h.ad j) ((Box.bar O B).bp j) := by
    intro u
    have k1 : Subtype.val ∘ (Ψ u).1 = (fun M : Matrix (Fin 3) (Fin 3) C' =>
        M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.om := rfl
    have k2 : ∀ v, Subtype.val ∘ (Ψ u).2 v = (fun M : Matrix (Fin 3) (Fin 3) C' =>
        M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.a v := fun v => rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      rw [k1]
      exact hom.2.2.1.comp _
    · intro v
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      rw [k2 v]
      exact (hom.2.2.2 v).comp _
    · intro s t r
      apply Subtype.ext
      exact borelProjection_isTwoCocycle hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker s t r
    · intro v s t
      exact pr_cocv hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker v s t
  refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ Ψ hmem), ?_⟩
  intro u hu C'' _ _ _ q p'' hcomp hq hy
  refine pr_obs hF O R ρ B hU hOf hCont hGood C' p D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker ?_
    C'' q p'' hcomp hq hy
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
  obtain ⟨β, Y, hβ, h1, h3⟩ := hu
  refine ⟨fun g => (β g : Matrix (Fin 3) (Fin 3) (ResidueField O)),
    fun v => (Y v : Matrix (Fin 3) (Fin 3) (ResidueField O)), hβ.comp _, ?_, ?_⟩
  · funext x
    exact congrArg (fun f => (f x : Matrix (Fin 3) (Fin 3) (ResidueField O))) h1
  · intro v s
    exact h3 v s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExtA
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ext_A :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [Algebra O C] (ξ ξ' : S.A →ₐ[O] C), S.u.map (ξ : S.A →+* C) = S.u.map (ξ' : S.A →+* C) → S.x0 ≤ (maximalIdeal C).comap (ξ : S.A →+* C) → S.x0 ≤ (maximalIdeal C).comap (ξ' : S.A →+* C) → ξ = ξ' := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ _ ξ ξ' hu h1 h2
  obtain ⟨-, -, -, hc⟩ := UpperTheory.V.Fr.cont_u hF hn S
  let E : Subalgebra O S.R := (AlgHom.equalizer ξ ξ').map S.A.val
  have hE : ∀ a : S.A, (a : S.R) ∈ E ↔ ξ a = ξ' a := fun a =>
    ⟨fun ⟨b, hb, h⟩ => (Subtype.ext h : b = a) ▸ hb, fun h => ⟨a, h, rfl⟩⟩
  have hr : ∀ g i j, S.ρ.r g i j ∈ E := fun g i j =>
    (hE (S.u.r g i j)).2 (congrArg (fun ρ : NRep F n C => ρ.r g i j) hu)
  have hψ : ∀ v i g, (S.ρ.ψ v i g : S.R) ∈ E := fun v i g =>
    (hE (S.u.ψ v i g : S.A)).2 (congrArg (fun ρ : NRep F n C => (ρ.ψ v i g : C)) hu)
  have h0 : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ E := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨L, -, rfl⟩ | ⟨v, i, g, rfl⟩)
    · refine Subalgebra.list_prod_mem E fun y hy => ?_
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact hr _ _ _
    · exact hψ v i g
  have hpow : ∀ (f : S.A →ₐ[O] C), S.x0 ≤ (maximalIdeal C).comap (f : S.A →+* C) → ∀ (N : ℕ) (a : S.A),
      a ∈ S.mB ^ N • S.gr 0 → f a ∈ maximalIdeal C ^ N := by
    intro f hf N a ha
    refine Submodule.smul_induction_on ha (fun b hb y _ => ?_) fun x y hx hy => ?_
    · rw [Algebra.smul_def, map_mul]
      refine Ideal.mul_mem_right _ _ ?_
      have h3 : algebraMap S.B S.A b ∈ S.x0 ^ N := by
        have := Ideal.mem_map_of_mem (S.inc : S.B →+* S.A) hb
        rw [Ideal.map_pow] at this
        exact this
      have h4 := Ideal.pow_right_mono hf N h3
      exact Ideal.le_comap_pow (f : S.A →+* C) N h4
    · rw [map_add (f := _)]
      exact add_mem hx hy
  have hB : S.B ≤ E := by
    intro b hb
    refine (hE ⟨b, S.B_le_A hb⟩).2 ?_
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal C) (maximalIdeal.isMaximal C).ne_top, Ideal.mem_iInf]
    intro N
    obtain ⟨M, hM⟩ := hc 0 N
    obtain ⟨y, hy, hby⟩ := hb M
    have hyB : y ∈ S.B := le_adicClosure _ hy
    have hg : S.inc ⟨b - y, sub_mem hb hyB⟩ ∈ S.gr 0 := by
      have h5 : (1 : S.A) ∈ S.gr 0 := Submodule.subset_span ⟨[], by simp, by simp⟩
      have h6 := Submodule.smul_mem _ (⟨b - y, sub_mem hb hyB⟩ : S.B) h5
      rw [Algebra.smul_def, mul_one] at h6
      exact h6
    have hm := hM _ hg hby
    have he : ξ ⟨y, S.B_le_A hyB⟩ = ξ' ⟨y, S.B_le_A hyB⟩ := (hE _).1 (h0 hy)
    have hs : (⟨b, S.B_le_A hb⟩ : S.A) = S.inc ⟨b - y, sub_mem hb hyB⟩ + ⟨y, S.B_le_A hyB⟩ :=
      Subtype.ext (sub_add_cancel b y).symm
    rw [hs, map_add (f := _), map_add (f := _), he, add_sub_add_right_eq_sub]
    exact sub_mem (hpow ξ h1 N _ hm) (hpow ξ' h2 N _ hm)
  have hA : S.A ≤ E := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · exact hB hx
    · exact hr g i j
  exact AlgHom.ext fun a => (hE a).1 (hA a.2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameFiberEq
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frame_fiber_eq :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (I : Ideal S.A), S.x0 ≤ I → ∃ f : ResidueField O →+* S.A ⧸ I, (S.u.map (Ideal.Quotient.mk I)).IsBar f ∧ (∀ i j, IsLocallyConstant fun g => (S.u.map (Ideal.Quotient.mk I)).r g i j) ∧ Subring.closure (Set.range f ∪ {x | ∃ g i j, x = (S.u.map (Ideal.Quotient.mk I)).r g i j}) = ⊤ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S I hI
  have hB : ∀ b : S.B, (b : S.R) ∈ maximalIdeal S.R → S.inc b ∈ I := fun b hb =>
    hI (Ideal.mem_map_of_mem _ (show b ∈ S.mB from hb))
  have hm : ∀ a ∈ maximalIdeal O, algebraMap O S.A a ∈ I := fun a ha =>
    hB (algebraMap O S.B a) (map_nonunit (algebraMap O S.R) a ha)
  let f : ResidueField O →+* S.A ⧸ I :=
    Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk I).comp (algebraMap O S.A))
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hm a ha)
  have hf : ∀ a : O, f (residue O a) = Ideal.Quotient.mk I (algebraMap O S.A a) := fun a => rfl
  have key : ∀ b : S.B, Ideal.Quotient.mk I (S.inc b) = f (res O S.R b) := fun b => by
    obtain ⟨a, ha⟩ := residue_surjective (res O S.R b)
    rw [← ha, hf, Ideal.Quotient.eq]
    have h1 : ((b - algebraMap O S.B a : S.B) : S.R) ∈ maximalIdeal S.R := by
      rw [← res_eq_zero_iff O]
      show res O S.R ((b : S.R) - algebraMap O S.R a) = 0
      rw [map_sub, AlgHom.commutes, ← ha]
      exact sub_self _
    have h2 := hB _ h1
    rwa [map_sub, AlgHom.commutes] at h2
  refine ⟨f, ⟨fun g i => ?_, fun v i g => ?_⟩, fun i j => ?_, ?_⟩
  · exact (key (S.aB g i)).trans (congrArg f (S.lift.2.1.1 g i))
  · exact (key (S.ψB v i g)).trans (congrArg f (S.lift.2.1.2 v i g))
  · have hle : S.x0 ^ 1 ≤ I := by rwa [pow_one]
    exact ((cont_u hF hn S).1.1 i j 1).comp (Ideal.Quotient.factor hle)
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨g, i, j, rfl⟩
      · exact Subring.subset_closure (Or.inl ⟨_, (key ⟨x, hx⟩).symm⟩)
      · exact Subring.subset_closure (Or.inr ⟨g, i, j, rfl⟩)
    | algebraMap a => exact Subring.subset_closure (Or.inl ⟨_, hf a⟩)
    | add x y hx hy h1 h2 => exact add_mem h1 h2
    | mul x y hx hy h1 h2 => exact mul_mem h1 h2
end

