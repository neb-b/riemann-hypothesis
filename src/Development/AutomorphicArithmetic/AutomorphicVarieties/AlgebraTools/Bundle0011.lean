module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ResNormal
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem pq_iff (l : ℕ) (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

private theorem res_map (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] (f : G →* G)
    (hf : Continuous f) {x : G} (hx : x ∈ proLRes l G) : f x ∈ proLRes l G := by
  rw [mem_proLRes] at hx ⊢
  intro N hN
  let M : OpenNormalSubgroup G :=
    { toSubgroup := (N.toOpenSubgroup : Subgroup G).comap f
      isOpen' := N.toOpenSubgroup.isOpen.preimage hf
      isNormal' := Subgroup.Normal.comap inferInstance f }
  have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
    rw [pq_iff] at hN ⊢
    intro g
    obtain ⟨k, hk⟩ := hN (f g)
    exact ⟨k, by simpa [M, map_pow] using hk⟩
  have := hx M hM
  simpa [M] using this

private theorem res_pow (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) (h : proLRes l G ≤ K) (g : G) :
    ∃ k : ℕ, g ^ l ^ k ∈ K := by
  classical
  let ι := {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))}
  let t : ι → Set G := fun i => ((i.1.toOpenSubgroup : Subgroup G) : Set G)
  have ht : ∀ i, IsClosed (t i) := fun i => i.1.toOpenSubgroup.isClosed
  have hs : IsCompact ((K : Set G)ᶜ) := (hK.isClosed_compl).isCompact
  have hdisjoint : Disjoint (K : Set G)ᶜ (⋂ i, t i) := by
    simp only [Set.disjoint_left, Set.mem_compl_iff, Set.mem_iInter]
    intro y hy hall
    apply hy
    apply h
    rw [mem_proLRes]
    intro N hN
    exact hall ⟨N, hN⟩
  obtain ⟨u, hu⟩ := hs.elim_finite_subfamily_closed t ht hdisjoint
  have hk : ∀ i : ι, ∃ k : ℕ, g ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G) := fun i =>
    (pq_iff l G _).mp i.2 g
  choose kf hkf using hk
  refine ⟨∑ i ∈ u, kf i, ?_⟩
  by_contra hg
  apply Set.disjoint_left.mp hu hg
  simp only [Set.mem_iInter]
  intro i hi
  have hle : kf i ≤ ∑ j ∈ u, kf j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  have heq : l ^ (∑ j ∈ u, kf j) = l ^ kf i * l ^ (∑ j ∈ u, kf j - kf i) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  show g ^ l ^ (∑ j ∈ u, kf j) ∈ ((i.1.toOpenSubgroup : Subgroup G) : Set G)
  rw [heq, pow_mul]
  exact Subgroup.pow_mem _ (hkf i) _

theorem UpperTheory.V.AlgebraTools.proLResOf_normal :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (H : Subgroup G) [H.Normal], IsClosed (H : Set G) →
      (proLResOf l H).Normal ∧ IsClosed (proLResOf l H : Set G) ∧ proLResOf l H ≤ H ∧
      ∀ (O : OpenNormalSubgroup G), proLResOf l H ≤ O.toSubgroup → ∀ h ∈ H, ∃ k : ℕ, h ^ l ^ k ∈ O.toSubgroup := by
  intro l _ G _ _ _ _ _ H _ hH
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    intro x hx g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let c : H →* H := (MulAut.conjNormal g).toMonoidHom
    have hc : Continuous c := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have := res_map l H c hc hy
    refine Subgroup.mem_map.mpr ⟨c y, this, ?_⟩
    simp [c, MulAut.conjNormal_apply]
  · unfold proLResOf
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hH.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_proLRes l H)
  · exact Subgroup.map_subtype_le _
  · intro O hO h hh
    have hle : proLRes l H ≤ (O.toOpenSubgroup : Subgroup G).comap H.subtype :=
      Subgroup.map_le_iff_le_comap.mp hO
    have hopen : IsOpen (((O.toOpenSubgroup : Subgroup G).comap H.subtype : Subgroup H) : Set H) :=
      O.toOpenSubgroup.isOpen.preimage continuous_subtype_val
    obtain ⟨k, hk⟩ := res_pow l H _ hopen hle ⟨h, hh⟩
    exact ⟨k, hk⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsBasic
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem units_x_mul_ep_and_st_idempotent_identities {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (i : ι) :
    U.x i * U.ep i = U.x i ∧ U.ep (o i) * U.x i = U.x i ∧ T.st (U.x i) * U.ep (o i) = T.st (U.x i) ∧ U.ep i * T.st (U.x i) = T.st (U.x i) := by
  have hr : U.x i * U.ep i = U.x i := by
    conv_rhs => rw [← U.x_mem i]
    conv_lhs => rw [← U.x_mem i]
    rw [mul_assoc _ (U.ep i) (U.ep i), (U.coi.idem i).eq]
  have hl : U.ep (o i) * U.x i = U.x i := by
    conv_rhs => rw [← U.x_mem i]
    conv_lhs => rw [← U.x_mem i]
    simp only [← mul_assoc, (U.coi.idem (o i)).eq]
  refine ⟨hr, hl, ?_, ?_⟩
  · have h := congrArg T.st hl
    rwa [T.st_mul, U.st_ep] at h
  · have h := congrArg T.st hr
    rwa [T.st_mul, U.st_ep] at h

theorem UpperTheory.V.AlgebraTools.units_basic :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o), (∀ i j, i ≠ j → U.x i * T.st (U.x j) = 0) ∧ ∑ i, T.st (U.x i) * U.x i = 1 ∧ (∀ i j y, i ≠ j → T.tr (U.ep i * y * U.ep j) = 0) ∧ (∀ y, T.tr y = ∑ i, T.tr (U.x i * y * T.st (U.x i))) ∧ (∀ i j y, o i = o j → U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep (o i)) ∧ (∀ y, y = ∑ i, ∑ j, T.st (U.x i) * (U.x i * y * T.st (U.x j)) * U.x j) ∧ ∀ i j y, U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o j) = U.x i * y * T.st (U.x j) := by
  intro B E _ _ _ T ι _ _ o U
  have key : ∀ i j y, U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o j) = U.x i * y * T.st (U.x j) := by
    intro i j y
    obtain ⟨-, hl, hs, -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U i
    obtain ⟨-, -, hs', -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U j
    simp only [← mul_assoc]
    rw [hl, mul_assoc _ (T.st (U.x j)), hs']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, key⟩
  · intro i j h
    obtain ⟨hr, -, -, -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U i
    obtain ⟨-, -, -, hs⟩ := units_x_mul_ep_and_st_idempotent_identities T o U j
    rw [← hr, ← hs, mul_assoc, ← mul_assoc (U.ep i), U.coi.ortho h, zero_mul, mul_zero]
  · simp_rw [U.st_mul_x_eq]
    exact U.coi.complete
  · intro i j y h
    rw [T.tr_comm, ← mul_assoc, U.coi.ortho (Ne.symm h), zero_mul, map_zero]
  · intro y
    have h : ∀ i, T.tr (U.x i * y * T.st (U.x i)) = T.tr (U.ep i * y) := by
      intro i
      rw [T.tr_comm, ← mul_assoc, U.st_mul_x_eq]
    simp_rw [h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Finset.sum_mul, U.coi.complete, one_mul]
  · intro i j y h
    have h7 := key i j y
    rw [← h] at h7
    calc U.x i * y * T.st (U.x j)
        = U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o i) := h7.symm
      _ = T.tr (U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o i)) • U.ep (o i) := U.corner_eq _ _
      _ = T.tr (U.x i * y * T.st (U.x j)) • U.ep (o i) := by rw [h7]
  · intro y
    have h : ∀ i j, T.st (U.x i) * (U.x i * y * T.st (U.x j)) * U.x j = U.ep i * y * U.ep j := by
      intro i j
      rw [← U.st_mul_x_eq i, ← U.st_mul_x_eq j]
      simp only [mul_assoc]
    simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul, U.coi.complete, mul_one, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsExist
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.units_exist :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {F : Type} [CommRing F] [Algebra B F] [HenselianRing B (RingHom.ker (algebraMap B F))] {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (r : E →ₐ[B] Matrix ι ι F) (ep : ι → E), IsUnit (2 : B) → (∀ i, o (o i) = o i) → (∀ x, r (T.st x) = (r x)ᵀ) → (∀ i, ∃ y, r y = single (o i) i 1) → CompleteOrthogonalIdempotents ep → (∀ i, T.st (ep i) = ep i) → (∀ i, r (ep i) = single i i 1) → (∀ i, T.tr (ep i) = 1) → (∀ i y, ∃ b : B, ep i * y * ep i = b • ep i) → ∃ U : T.Units ι o, U.ep = ep ∧ ∀ i, r (U.x i) = single (o i) i 1 := by
  intro B E _ _ _ T F _ _ _ ι _ _ o r ep h2 ho hr hy hco hst hre htr hrank
  have idem : ∀ i, ep i * ep i = ep i := fun i => (hco.idem i).eq
  have idem' : ∀ i x, ep i * (ep i * x) = ep i * x := fun i x => by rw [← mul_assoc, idem]
  choose y hy using hy
  obtain ⟨z, hz⟩ : ∃ z : ι → E, ∀ i, z i = ep (o i) * y i * ep i := ⟨_, fun i => rfl⟩
  have hz_mem : ∀ i, ep (o i) * z i * ep i = z i := by
    intro i
    rw [hz]
    simp only [mul_assoc, idem, idem']
  have hstz : ∀ i, T.st (z i) = ep i * (T.st (y i) * ep (o i)) := by
    intro i
    rw [hz, T.st_mul, T.st_mul, hst, hst]
  have hrz : ∀ i, r (z i) = single (o i) i 1 := by
    intro i
    rw [hz, map_mul, map_mul, hre, hre, hy]
    simp only [Matrix.single_mul_single_same, mul_one]
  choose b hb using fun i => hrank i (T.st (y i) * ep (o i) * y i)
  choose b' hb2 using fun i => hrank (o i) (y i * ep i * T.st (y i))
  have hb' : ∀ i, T.st (z i) * z i = b i • ep i := by
    intro i
    rw [hstz, hz, ← hb i]
    simp only [mul_assoc, idem, idem']
  have hzst : ∀ i, z i * T.st (z i) = b' i • ep (o i) := by
    intro i
    rw [hstz, hz, ← hb2 i]
    simp only [mul_assoc, idem, idem']
  have hbb : ∀ i, b' i = b i := by
    intro i
    have h := congrArg T.tr (hzst i)
    rw [T.tr_comm, hb', map_smul, map_smul, htr, htr, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h
    exact h.symm
  have hbF : ∀ i, algebraMap B F (b i) = 1 := by
    intro i
    have h := congrArg r (hb' i)
    rw [map_mul, hr, hrz, map_smul, hre, Matrix.transpose_single, Matrix.single_mul_single_same,
      mul_one] at h
    have h' := congrArg (fun M : Matrix ι ι F => M i i) h
    simp only [Matrix.smul_apply, Matrix.single_apply_same, Algebra.smul_def, mul_one] at h'
    exact h'.symm
  have hb1 : ∀ i, b i - 1 ∈ RingHom.ker (algebraMap B F) := by
    intro i
    rw [RingHom.mem_ker, map_sub, hbF, map_one, sub_self]
  choose α hα hα1 using fun i => UpperTheory.V.AlgebraTools.sqrt_one_add (RingHom.ker (algebraMap B F)) (b i) h2 (hb1 i)
  have hαinvF : ∀ i, algebraMap B F (↑(α i)⁻¹ : B) = 1 := by
    intro i
    have h1 := hα1 i
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
    have h := congrArg (algebraMap B F) (Units.inv_mul (α i))
    rw [map_mul, map_one, h1, mul_one] at h
    exact h
  have hinv : ∀ i, (↑(α i)⁻¹ : B) * ↑(α i)⁻¹ * b i = 1 := by
    intro i
    rw [← hα, sq, mul_assoc, ← mul_assoc (↑(α i)⁻¹ : B) (↑(α i)) (↑(α i)), Units.inv_mul, one_mul,
      Units.inv_mul]
  refine ⟨⟨ep, fun i => if o i = i then ep i else (↑(α i)⁻¹ : B) • z i, ho, hco, hst, htr, hrank,
    ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, h, idem, idem]
    · rw [if_neg h, mul_smul_comm, smul_mul_assoc, hz_mem]
  · intro i
    rw [if_pos (ho i)]
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, hst, idem, h]
    · rw [if_neg h, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hzst, hbb, smul_smul, hinv,
        one_smul]
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, hst, idem]
    · rw [if_neg h, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hb', smul_smul, hinv, one_smul]
  · intro i
    dsimp only
    by_cases h : o i = i
    · rw [if_pos h, hre, h]
    · rw [if_neg h, map_smul, hrz, ← algebraMap_smul (A := F), hαinvF, one_smul]
end

