module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Formalism.SharpRestriction.GrowthBounds.WittFrameLocaliserOrders
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ColSpanMap
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G

section Incl

variable (W Qq : Type) [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]

def incl (k : ℕ) : (Fin k → W) →ₗ[W] (Fin k → Qq) := (Algebra.linearMap W Qq).compLeft (Fin k)

variable {W Qq}

theorem incl_apply {k : ℕ} (y : Fin k → W) (i : Fin k) : incl W Qq k y i = algebraMap W Qq (y i) := rfl

theorem incl_inj [IsFractionRing W Qq] (k : ℕ) : Function.Injective (incl W Qq k) := by
  intro x y h
  funext i
  have h1 := congrFun h i
  rw [incl_apply, incl_apply] at h1
  exact IsFractionRing.injective W Qq h1

theorem colSpan_map {k : ℕ} (M : Matrix (Fin k) (Fin k) W) :
    colSpan W (M.map (algebraMap W Qq)) =
      (Submodule.span W (Set.range fun c : Fin k => fun i => M i c)).map (incl W Qq k) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem colSpan_one (k : ℕ) :
    colSpan W (1 : Matrix (Fin k) (Fin k) Qq) = LinearMap.range (incl W Qq k) := by
  have h1 : (1 : Matrix (Fin k) (Fin k) Qq) = (1 : Matrix (Fin k) (Fin k) W).map (algebraMap W Qq) :=
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  rw [h1, colSpan_map, LinearMap.range_eq_map]
  congr 1
  rw [← (Pi.basisFun W (Fin k)).span_eq]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    funext i
    simp [Matrix.one_apply, Pi.single_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    funext i
    simp [Matrix.one_apply, Pi.single_apply]

theorem lattice_of [IsPrincipalIdealRing W] [IsFractionRing W Qq] (p k : ℕ) (hp0 : (p : W) ≠ 0)
    (N : Submodule W (Fin k → W)) (hpN : ∀ x, (p : W) • x ∈ N) : IsLattice W (N.map (incl W Qq k)) := by
  classical
  haveI : Module.Free W N := Module.Free.of_basis (Submodule.basisOfPid (Pi.basisFun W (Fin k)) N).2
  have hfin : Module.finrank W N = k := by
    apply le_antisymm
    · calc Module.finrank W N ≤ Module.finrank W (Fin k → W) := Submodule.finrank_le N
        _ = k := by simp
    · let f : (Fin k → W) →ₗ[W] N := LinearMap.codRestrict N ((p : W) • LinearMap.id) (fun c => by simpa using hpN c)
      have hinj : Function.Injective f := by
        intro x y hxy
        have h2 := congrArg Subtype.val hxy
        simp only [f, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2
        exact smul_right_injective (Fin k → W) hp0 h2
      have h3 := LinearMap.finrank_le_finrank_of_injective hinj
      simpa using h3
  let b' : Module.Basis (Fin k) W N := Module.finBasisOfFinrankEq W N hfin
  let M : Matrix (Fin k) (Fin k) W := fun i c => (b' c : Fin k → W) i
  have hspan : Submodule.span W (Set.range fun c => (b' c : Fin k → W)) = N := by
    have h1 := congrArg (Submodule.map N.subtype) b'.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
    exact h1
  let A : Matrix (Fin k) (Fin k) W := fun c i => b'.repr ⟨(p : W) • Pi.single i 1, hpN _⟩ c
  have hMA : M * A = (p : W) • (1 : Matrix (Fin k) (Fin k) W) := by
    ext a i
    have hx := congrArg (fun v : N => (v : Fin k → W) a) (b'.sum_repr ⟨(p : W) • Pi.single i 1, hpN _⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply] at hx
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ← hx]
    exact Finset.sum_congr rfl (fun c _ => by simp only [M, A]; ring)
  have hdetM : M.det ≠ 0 := by
    intro h0
    have h4 := congrArg Matrix.det hMA
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h4
    exact pow_ne_zero k hp0 h4.symm
  refine ⟨M.map (algebraMap W Qq), ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).mpr hdetM
  · rw [colSpan_map]
    congr 1
    exact hspan.symm

theorem card_quot [IsFractionRing W Qq] (k : ℕ) (T : Submodule W (Fin k → Qq))
    (hT : T = LinearMap.range (incl W Qq k)) (N : Submodule W (Fin k → W)) :
    Nat.card (↥T ⧸ Submodule.comap T.subtype (N.map (incl W Qq k))) = Nat.card ((Fin k → W) ⧸ N) := by
  subst hT
  refine Nat.card_congr (Submodule.Quotient.equiv N _ (LinearEquiv.ofInjective (incl W Qq k) (incl_inj k)) ?_).toEquiv.symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have h1 := congrArg Subtype.val hxy
    simpa [LinearEquiv.ofInjective_apply] using h1
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    simpa [LinearEquiv.ofInjective_apply] using hxy

end Incl

section Psi

variable {W : Type} [CommRing W]

def psi {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) : (Fin (r + K) → W) →ₗ[W] (Fin r → W ⧸ I) :=
  LinearMap.pi fun i =>
    (Submodule.mkQ I) ∘ₗ (LinearMap.proj (Fin.castAdd K i) + ∑ c, A i c • LinearMap.proj (Fin.natAdd r c))

theorem psi_apply {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) (y : Fin (r + K) → W) (i : Fin r) :
    psi I A y i = Ideal.Quotient.mk I (y (Fin.castAdd K i) + ∑ c, A i c * y (Fin.natAdd r c)) := by
  simp [psi, LinearMap.sum_apply]

theorem psi_surj {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) : Function.Surjective (psi I A) := by
  intro z
  choose f hf using fun i => Ideal.Quotient.mk_surjective (I := I) (z i)
  refine ⟨Fin.append f 0, ?_⟩
  funext i
  rw [psi_apply, Fin.append_left]
  simp [Fin.append_right, hf]

theorem psi_smul {r K : ℕ} (I : Ideal W) (a : W) (ha : a ∈ I) (A : Fin r → Fin K → W) (x : Fin (r + K) → W) :
    a • x ∈ LinearMap.ker (psi I A) := by
  rw [LinearMap.mem_ker, map_smul]
  funext i
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (psi I A x i)
  rw [Pi.smul_apply, ← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul, Pi.zero_apply]

theorem psi_ker_inj {r K : ℕ} (I : Ideal W) (A B : Fin r → Fin K → W)
    (h : LinearMap.ker (psi I A) = LinearMap.ker (psi I B)) (i : Fin r) (c : Fin K) :
    Ideal.Quotient.mk I (A i c) = Ideal.Quotient.mk I (B i c) := by
  have key : ∀ Z : Fin r → Fin K → W, ∀ i', psi I Z (Fin.append (fun i'' => -A i'' c) (Pi.single c 1)) i' =
      Ideal.Quotient.mk I (-A i' c + Z i' c) := by
    intro Z i'
    rw [psi_apply, Fin.append_left]
    congr 1
    simp [Fin.append_right, Pi.single_apply]
  have hA : Fin.append (fun i'' => -A i'' c) (Pi.single c 1) ∈ LinearMap.ker (psi I A) := by
    rw [LinearMap.mem_ker]
    funext i'
    rw [key, Pi.zero_apply]
    simp
  rw [h, LinearMap.mem_ker] at hA
  have h1 := congrFun hA i
  rw [key, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [eq_comm, Ideal.Quotient.eq]
  convert h1 using 1
  ring

end Psi

theorem manyEdges : ManyEdges := by
  classical
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS k r hrk
  obtain ⟨K, rfl⟩ : ∃ K, k = r + K := ⟨k - r, by omega⟩
  haveI := hS.frac_alt
  set I : Ideal W := Ideal.span {(p : W)} with hI
  have hpI : (p : W) ∈ I := Ideal.mem_span_singleton_self _
  have hp0 : (p : W) ≠ 0 := hS.p_unif.ne_zero
  have hcard : Nat.card (W ⧸ I) = p ^ n' := hS.res_card
  haveI : Finite (W ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hS.prime.ne_zero)
  haveI : Fintype (W ⧸ I) := Fintype.ofFinite _
  choose lift hlift using (Ideal.Quotient.mk_surjective (I := I))
  let ed : (Fin r → Fin K → W ⧸ I) → Edge W Qq (r + K) := fun A =>
    ⟨(LinearMap.ker (psi I (fun i c => lift (A i c)))).map (incl W Qq (r + K)),
      colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq)⟩
  have hinj : Function.Injective ed := by
    intro A B hAB
    have h1 := congrArg Edge.src hAB
    have h2 := Submodule.map_injective_of_injective (incl_inj (W := W) (Qq := Qq) (r + K)) h1
    funext i c
    have h3 := psi_ker_inj I _ _ h2 i c
    rwa [hlift, hlift] at h3
  refine ⟨Finset.univ.image ed, ?_, ?_⟩
  · intro e he
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp he
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · exact lattice_of (Qq := Qq) p (r + K) hp0 _ (fun x => psi_smul I (p : W) hpI _ x)
    · exact ⟨1, by simp, rfl⟩
    · show _ ≤ colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq)
      rw [colSpan_one]
      exact LinearMap.map_le_range
    · intro x hx
      change x ∈ colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq) at hx
      rw [colSpan_one] at hx
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
      exact Submodule.mem_map.mpr ⟨(p : W) • y, psi_smul I (p : W) hpI _ y, map_smul _ _ _⟩
    · refine (card_quot (r + K) _ (colSpan_one (r + K)) _).trans ?_
      rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ (psi_surj I _)).toEquiv]
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard,
        ← pow_mul]
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard, Nat.add_sub_cancel_left,
      ← pow_mul, ← pow_mul]
    apply le_of_eq
    congr 1
    ring

end Formalism.MainNotions.Pf14
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.FramesOf
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

def FramesOK {n' r : ℕ} [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ N₁ G' : ℕ) (F : Frames n' r) : Prop :=
  F.TT = TT ∧ F.Valid L₁ N₁ ∧ (∀ j : ℤ, F.fr j (r - 1) - F.fr (j - 1) 0 < G') ∧
    (∀ j : ℤ, ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
        (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → F.GapGt L₂ j x) ∧
    (∀ j : ℤ, F.GapGt L₂ j (F.fr j 0))

theorem de_pos_of {L₂ : ℕ} {de : ℝ} (h : L₂ < goodU de) : 0 < de := by
  by_contra hde
  have h1 : 1 / de ≤ 0 := by
    apply div_nonpos_of_nonneg_of_nonpos zero_le_one (not_lt.1 hde)
  have : goodU de = 0 := by
    unfold goodU
    exact Nat.ceil_eq_zero.2 h1
  omega

theorem frames_of {n' : ℕ} [NeZero n'] (TT : Finset (Fin n')) (r L₁ L₂ : ℕ) (de h x : ℝ) (hn : Even n')
    (hr : 2 ≤ r) (hL1 : 1 ≤ L₁) (hO : tableLineDegreeFive.OrbitHyp n' TT r L₁ L₂ de h x) :
    ∃ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F := by
  obtain ⟨hgood, hL12, hLu, h3G⟩ := hO
  have hde : 0 < de := de_pos_of hLu
  have hg := hgood
  obtain ⟨_, hTiles, _⟩ := hgood
  have hu : 1 ≤ goodU de := bd_goodU_pos hde
  have hell : 0 < (6 * r + 1) * goodU de := Nat.mul_pos (by omega) hu
  have hGdef : goodG' r de h x = (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) := rfl
  have hMt : orbitSmallMultiplicity r h x + 1 < n' / ((6 * r + 1) * goodU de) := by
    have h1 : (orbitSmallMultiplicity r h x + 2) * ((6 * r + 1) * goodU de) ≤ n' := by
      have h2 : (orbitSmallMultiplicity r h x + 2) * ((6 * r + 1) * goodU de) ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [hGdef] at h3G
      omega
    exact (Nat.le_div_iff_mul_le hell).2 h1
  obtain ⟨J, B, sidx, hS⟩ := bf_seq TT r (goodU de) (orbitSmallMultiplicity r h x) hn hu hTiles hMt
  obtain ⟨F, hTT, v1, v2, v3, v4, v5, v6, v7, c1, c2, c3, c4, c5⟩ :=
    bf_frames TT r (goodU de) L₂ (goodG' r de h x) (orbitSmallMultiplicity r h x) J B sidx hr hu hLu
      (by rw [hGdef]; exact Nat.mul_le_mul_right _ (by omega)) hS
  subst hTT
  have hL2n : L₂ ≤ n' := by have := bd_U_le_G' r de h x; omega
  have hI := fun y => bd_orbit_interval F.TT L₂ (r - 1) r de h x hL2n hg y
  have hcardL := fun j => bd_letters_card F L₂ (r - 1) r de h x (by omega) hg j (c3 j)
  have hLL : L₁ ≤ L₂ := by omega
  exact ⟨F, rfl, ⟨v1, v2, v3, v4, v5, v6,
      fun j => ⟨(v7 j).1, fun x hx hc => ⟨(v7 j).2 x hx hc, bd_gap_mono F hLL (c4 j x hx hc)⟩,
        bd_gap_mono F hLL (c5 j)⟩,
      hcardL,
      fun j x _ hw => bd_oldest_far F L₁ L₂ (by omega) (by omega) hI j x
        (bd_vectors_before F (by omega) v3 v4 v5 j x hw)⟩, c3, c4, c5⟩

end Formalism.MainNotions.Pf14
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.GoodRankOfPrim
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section Ring

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem p_nonunit (hS : HidaSetting p n' W Qq O Kf ι σ j w) : ¬ IsUnit (p : O) := by
  intro hu
  let _ : Algebra W O := j.toAlgebra
  have _ : Module.Finite W O := hS.finite
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := W) (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (IsLocalRing.maximalIdeal O)
  have heq : (IsLocalRing.maximalIdeal O).comap (algebraMap W O) = IsLocalRing.maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal hmax
  have hpW : (p : W) ∈ IsLocalRing.maximalIdeal W := hS.p_unif.not_isUnit
  rw [← heq, Ideal.mem_comap, map_natCast] at hpW
  exact hpW hu

end Ring

theorem goodRank_of_prim {O Kf X : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup X] [Module O X]
    (hinj : Function.Injective (algebraMap O Kf)) (π : O) (A : Submodule O X) {M : ℕ} (φ : Fin M → X → Kf) (D : ℕ)
    (hadd : ∀ i G G', φ i (G + G') = φ i G + φ i G')
    (hsmul : ∀ i (c : O) G, φ i (c • G) = algebraMap O Kf c * φ i G)
    (hint : ∀ i, ∀ G ∈ A, φ i G ∈ Set.range (algebraMap O Kf))
    (hprim : ∀ c : Fin M → O, (∃ i, IsUnit (c i)) →
      ∃ G ∈ A, ValLe π D (∑ i, algebraMap O Kf (c i) * φ i G)) :
    GoodRankK π A φ M D := by
  classical
  have h0 : ∀ i, φ i 0 = 0 := fun i => by
    have h := hadd i 0 0
    rw [add_zero] at h
    linear_combination -h
  let S : Submodule O (Fin M → O) :=
    { carrier := {v | ∃ G ∈ A, ∀ i, algebraMap O Kf (v i) = φ i G}
      add_mem' := by
        rintro v v' ⟨G, hG, hv⟩ ⟨G', hG', hv'⟩
        exact ⟨G + G', A.add_mem hG hG', fun i => by rw [Pi.add_apply, map_add (f := _), hv, hv', hadd]⟩
      zero_mem' := ⟨0, A.zero_mem, fun i => by rw [Pi.zero_apply, map_zero, h0]⟩
      smul_mem' := by
        rintro c v ⟨G, hG, hv⟩
        exact ⟨c • G, A.smul_mem c hG, fun i => by rw [Pi.smul_apply, smul_eq_mul, map_mul, hv, hsmul]⟩ }
  have hS : ∀ c : Fin M → O, (∃ i, IsUnit (c i)) → ∃ s ∈ S, (∑ i, c i * s i) ∣ π ^ D := by
    intro c hc
    obtain ⟨G, hG, a, b, hab, hb⟩ := hprim c hc
    choose v hv using fun i => hint i G hG
    refine ⟨v, ⟨G, hG, hv⟩, ?_⟩
    have hsum : ∑ i, c i * v i = a := hinj (by rw [← hab, map_sum]; simp only [map_mul, hv])
    exact ⟨b, by rw [hsum, hb]⟩
  have hmem : ∀ k : Fin M, π ^ D • Pi.single k (1 : O) ∈ S := fun k => smith_mem S (π ^ D) hS _
  choose G hGA hG using hmem
  have hsumφ : ∀ i (s : Finset (Fin M)) (f : Fin M → X), φ i (∑ k ∈ s, f k) = ∑ k ∈ s, φ i (f k) :=
    fun i s f => map_sum (AddMonoidHom.mk' (φ i) (hadd i)) f s
  let u : (Fin M → O) →ₗ[O] A :=
    { toFun := fun x => ∑ k, x k • (⟨G k, hGA k⟩ : A)
      map_add' := fun x y => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have key : ∀ x i, φ i (u x : X) = algebraMap O Kf (π ^ D * x i) := by
    intro x i
    have hu : (u x : X) = ∑ k, x k • G k := by simp [u]
    rw [hu, hsumφ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hsmul, ← hG, ← map_mul, ← map_sum]
    congr 1
    simp [Pi.single_apply, mul_comm]
  refine ⟨u, 1, fun x k => ?_⟩
  simp [key, Matrix.one_apply]

section Be

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}

theorem be_add_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0)
    (G G' : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (G + G') = be p r lam0 F G + be p r lam0 F G' := by
  simp only [be, LinearMap.add_apply]

theorem be_smul_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0) (c : O)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (c • G) = algebraMap O Kf c * be p r lam0 F G := by
  simp only [be, LinearMap.smul_apply, Algebra.smul_def]

theorem be_smulK_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0) (c : Kf)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (c • G) = c * be p r lam0 F G := by
  simp only [be, LinearMap.smul_apply, smul_eq_mul]

theorem be_sum_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) {n : ℕ} (c : Fin n → O) (F : Fin n → Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) :
    be p r lam0 (∑ i, c i • F i) G = ∑ i, algebraMap O Kf (c i) * be p r lam0 (F i) G := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [be, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul Kf (c i) (F i), smul_smul, mul_comm, ← smul_smul, map_smul, smul_eq_mul]

end Be

theorem s7 : S7 := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS hBP m r lam0 t D κ cStar L hdom hc hsrc
  classical
  have _ := hS.frac_O
  obtain ⟨E, nE, F, hE, hFsrc, hFoth, hprim, hcard⟩ := hsrc
  have hRe : ∀ e ∈ E, ∀ i, F e i ∈ Re p ι σ w r lam0 e := by
    intro e he i
    have h := (Submodule.mem_inf.mp (hFsrc e he i)).2
    rw [Submodule.mem_iInf] at h
    exact (Submodule.mem_iInf _).mp (h e) ⟨(hE e he).1, rfl⟩
  let T := Σ e : E, Fin (nE e.1)
  let eqv : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T, fun k => (eqv k).1.1, fun k => F (eqv k).1.1 (eqv k).2,
    fun k => hE _ (eqv k).1.2, fun k => hFsrc _ (eqv k).1.2 _,
    fun k e' he' hs' hne => hFoth _ (eqv k).1.2 _ e' he' hs' hne, Fintype.card T, ?_, ?_⟩
  · have hT : Fintype.card T = ∑ e ∈ E, nE e := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact Finset.sum_coe_sort E nE
    rw [hT]
    exact hcard
  refine goodRank_of_prim (IsFractionRing.injective O Kf) (p : O) _ _ D
    (fun k G G' => be_add_right p r lam0 _ G G') (fun k c G => be_smul_right p r lam0 _ c G) ?_ ?_
  · intro k G hG
    have he := hE _ (eqv k).1.2
    have hG' : G ∈ Re' p ι σ w r lam0 (eqv k).1.1 := by
      have h := (Submodule.mem_inf.mp hG).2
      rw [Submodule.mem_iInf] at h
      exact (Submodule.mem_iInf _).mp (h _) he
    exact ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom _ he.1).1 G).mp hG' _ (hRe _ (eqv k).1.2 _)
  · rintro c ⟨k0, hk0⟩
    obtain ⟨⟨e0, i0⟩, hx⟩ : ∃ x, eqv k0 = x := ⟨_, rfl⟩
    have hk0' : IsUnit (c (eqv.symm ⟨e0, i0⟩)) := by
      rw [← hx, Equiv.symm_apply_apply]
      exact hk0
    obtain ⟨G, hGN, hval, hGoth⟩ := hprim e0.1 e0.2 (fun i => c (eqv.symm ⟨e0, i⟩)) ⟨i0, hk0'⟩
    obtain ⟨a, b, hva, hab⟩ := hval
    refine ⟨G, hGN, ?_⟩
    have hterm : ∀ e : E, ∀ i : Fin (nE e.1), e ≠ e0 →
        ∃ z : O, be p r lam0 (F e.1 i) G = algebraMap O Kf ((p : O) ^ (D + 1) * z) := by
      intro e i hne
      have he := hE e.1 e.2
      obtain ⟨G₀, hG₀, hGeq⟩ := Submodule.mem_map.mp (hGoth e.1 e.2 (fun h => hne (Subtype.ext h)))
      obtain ⟨y, hy⟩ := ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom _ he.1).1 G₀).mp hG₀ _ (hRe _ e.2 i)
      refine ⟨w ^ (cStar - 2 * (D + 1)) * y, ?_⟩
      rw [← hGeq, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, be_smulK_right, ← hy, zpow_natCast,
        ← map_pow, ← map_mul, ← hS.w_sq, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 3
      omega
    have hsplit : ∑ k, algebraMap O Kf (c k) * be p r lam0 (F (eqv k).1.1 (eqv k).2) G =
        be p r lam0 (∑ i, c (eqv.symm ⟨e0, i⟩) • F e0.1 i) G +
          ∑ e ∈ Finset.univ.erase e0, ∑ i, algebraMap O Kf (c (eqv.symm ⟨e, i⟩)) * be p r lam0 (F e.1 i) G := by
      have h1 : ∑ k, algebraMap O Kf (c k) * be p r lam0 (F (eqv k).1.1 (eqv k).2) G =
          ∑ x : T, algebraMap O Kf (c (eqv.symm x)) * be p r lam0 (F x.1.1 x.2) G :=
        Fintype.sum_equiv eqv _ _ (fun k => by rw [Equiv.symm_apply_apply])
      rw [h1, Fintype.sum_sigma, be_sum_left, ← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
    have hrest : ∃ z : O, (∑ e ∈ Finset.univ.erase e0, ∑ i,
        algebraMap O Kf (c (eqv.symm ⟨e, i⟩)) * be p r lam0 (F e.1 i) G) = algebraMap O Kf ((p : O) ^ (D + 1) * z) := by
      refine Finset.sum_induction _ (fun x => ∃ z : O, x = algebraMap O Kf ((p : O) ^ (D + 1) * z))
        (fun x y ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ => ⟨z₁ + z₂, by rw [h₁, h₂, mul_add, map_add (f := _)]⟩) ⟨0, by simp⟩ ?_
      intro e he
      refine Finset.sum_induction _ (fun x => ∃ z : O, x = algebraMap O Kf ((p : O) ^ (D + 1) * z))
        (fun x y ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ => ⟨z₁ + z₂, by rw [h₁, h₂, mul_add, map_add (f := _)]⟩) ⟨0, by simp⟩ ?_
      intro i _
      obtain ⟨z, hz⟩ := hterm e i (Finset.ne_of_mem_erase he)
      exact ⟨c (eqv.symm ⟨e, i⟩) * z, by rw [hz, ← map_mul]; congr 1; ring⟩
    obtain ⟨z, hz⟩ := hrest
    obtain ⟨b', hb'⟩ := dvd_of_add (p : O) (p_nonunit hS) D a z ⟨b, hab.symm⟩
    exact ⟨a + (p : O) ^ (D + 1) * z, b', by rw [hsplit, hva, hz, map_add (f := _)], hb'.symm⟩

end Formalism.MainNotions.Pf14
end
end

