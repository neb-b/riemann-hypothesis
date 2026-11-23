module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0056

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PushSel
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem adicCont_map {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] (j : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map j ≤ J) (f : Γ → R) (hf : AdicCont I f) :
    AdicCont J fun g => j (f g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap j := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono h N
  exact (hf N).comp (Ideal.quotientMap (J ^ N) j hN)

private theorem od_map {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) R} (h : Z ∈ Od R R n a) : Z.map j ∈ Od S S n a := by
  intro i k
  refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
  have := (h i k).1 e
  rw [Submodule.mem_bot] at this ⊢
  simp [this]

theorem UpperTheory.V.Pa.Det.pushSel :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → (∀ z ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a), (fun g => (z g).map j) ∈ SelZ F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)) ∧ (∀ z ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a), (fun g => (z g).map j) ∈ Bd F (x'.ρX x'.A) (Od x'.A x'.A n x'.a)) ∧ ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y → LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j) := by
  intro l _ F n x x' j hE
  obtain ⟨⟨-, hloc, -, hρ, ha, -⟩, hw, -⟩ := hE
  have eρ : ∀ g, x'.ρX x'.A g = j.mapMatrix (x.ρX x.A g) := by
    intro g
    ext i k : 1
    simp only [NP.ρX, hρ]
    rfl
  have ew : ∀ v, x'.wX x'.A v = j.mapMatrix (x.wX x.A v) := by
    intro v
    ext i k : 1
    simp only [NP.wX, hw]
    rfl
  have ewi : ∀ v, x'.wiX x'.A v = j.mapMatrix (x.wiX x.A v) := by
    intro v
    ext i k : 1
    simp only [NP.wiX, hw, ← map_inv]
    rfl
  have ed : ∀ Y g, dY F (x'.ρX x'.A) (Y.map j) g = j.mapMatrix (dY F (x.ρX x.A) Y g) := by
    intro Y g
    simp only [dY, eρ, map_sub, map_mul]
    rfl
  have hL : ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y →
      LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j) := by
    intro z v Y h g
    have key : x'.wiX x'.A v * ((z (F.φ v g)).map j - dY F (x'.ρX x'.A) (Y.map j) (F.φ v g)) * x'.wX x'.A v
        = j.mapMatrix (x.wiX x.A v * (z (F.φ v g) - dY F (x.ρX x.A) Y (F.φ v g)) * x.wX x.A v) := by
      rw [ed, ew, ewi, map_mul, map_mul, map_sub]
      rfl
    refine ⟨fun i k hik => ?_, fun hg i => ?_⟩
    · simp only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).1 i k hik, map_zero]
    · simp only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).2 hg i, map_zero]
  have ht : (Ideal.span {algebraMap x.A x.A x.t}).map j ≤ Ideal.span {algebraMap x'.A x'.A x'.t} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    change (PowerSeries.X : PowerSeries x'.K) ∣ j PowerSeries.X
    rw [PowerSeries.X_dvd_iff]
    by_contra hne
    have hu : IsUnit (j PowerSeries.X) := PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne)
    have hX := PowerSeries.isUnit_iff_constantCoeff.1 (hloc.map_nonunit _ hu)
    simp at hX
  refine ⟨?_, ?_, hL⟩
  · rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => ha ▸ od_map j (h1 g), fun i k => adicCont_map j _ _ ht _ (h2 i k), fun g h => ?_,
      fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
    · change j.mapMatrix (z (g * h)) = j.mapMatrix (z g) + _ * j.mapMatrix (z h) * _
      rw [h3, eρ, eρ, map_add (f := _), map_mul, map_mul]
    · ext i k : 1
      simp [h4]
    · simp [h5 u g hg]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      exact ⟨Y.map j, ha ▸ od_map j hY, hL z v Y hl⟩
  · rintro z ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map j, ha ▸ od_map j hY, ?_, ?_⟩
    · rw [← Matrix.transpose_map, hT]
      ext i k : 1
      simp
    · funext g
      exact (ed Y g).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.RelMove
section
noncomputable section

open Matrix

namespace UpperTheory.V.Pa.Det

private theorem der_mul {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (hz : TwCoc (fun _ => 1) D.r D.G' z) {g h : G} (hg : g ∈ D.G') (hh : h ∈ D.G') :
    z (g * h) * D.r (g * h) = z g * D.r g * D.r h + D.r g * (z h * D.r h) := by
  have h1 := hz g hg h hh
  simp only [one_smul] at h1
  have hinv : D.r g⁻¹ * D.r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [h1, map_mul, add_mul]
  congr 1
  · simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D.r g⁻¹), hinv, Matrix.one_mul]

private theorem move_one {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) (hz : TwCoc (fun _ => 1) D.r D.G' z) (hk : D.KillsRel z i j)
    (c : G →₀ F) (hc : ∀ g ∈ c.support, g ∈ D.G') (h0 : c.sum (fun g x => x • D.r g) = 0)
    {u v : G} (hu : u ∈ D.G') (hv : v ∈ D.G') :
    (D.r u * (c.sum fun g x => x • (z g * D.r g)) * D.r v) i j = 0 := by
  classical
  have hsum : ∀ M : G → Matrix (Fin n) (Fin n) F,
      (Finsupp.mapDomain (fun g => u * g * v) c).sum (fun g x => x • M g) = c.sum (fun g x => x • M (u * g * v)) := by
    intro M
    exact Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hsupp : ∀ g ∈ (Finsupp.mapDomain (fun g => u * g * v) c).support, g ∈ D.G' := by
    intro g hg
    obtain ⟨k, hk', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    exact D.G'.mul_mem (D.G'.mul_mem hu (hc k hk')) hv
  have hr : ∀ M : G → Matrix (Fin n) (Fin n) F, ∀ P Q : Matrix (Fin n) (Fin n) F,
      P * (c.sum fun g x => x • M g) * Q = c.sum fun g x => x • (P * M g * Q) := by
    intro M P Q
    simp only [Finsupp.sum, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have h0' : (Finsupp.mapDomain (fun g => u * g * v) c).sum (fun g x => x • D.r g) = 0 := by
    rw [hsum]
    simp only [map_mul]
    rw [← hr, h0, Matrix.mul_zero, Matrix.zero_mul]
  have key := hk _ hsupp h0'
  rw [hsum] at key
  have expand : ∀ g ∈ c.support, c g • (z (u * g * v) * D.r (u * g * v)) =
      c g • (z u * D.r u * D.r g * D.r v) + c g • (D.r u * (z g * D.r g) * D.r v) + c g • (D.r u * D.r g * (z v * D.r v)) := by
    intro g hg
    rw [mul_assoc, der_mul D z hz hu (D.G'.mul_mem (hc g hg) hv), der_mul D z hz (hc g hg) hv, ← smul_add, ← smul_add]
    congr 1
    simp only [map_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
  have eq : (c.sum fun g x => x • (z (u * g * v) * D.r (u * g * v))) =
      z u * D.r u * (c.sum fun g x => x • D.r g) * D.r v + D.r u * (c.sum fun g x => x • (z g * D.r g)) * D.r v
        + D.r u * (c.sum fun g x => x • D.r g) * (z v * D.r v) := by
    rw [hr, hr, hr]
    simp only [Finsupp.sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl expand
  rw [eq, h0] at key
  simpa using key

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (i i' : Fin n) (h : (i : ℕ) < a ↔ (i' : ℕ) < a) :
    Matrix.single i i' (1 : F) ∈ Ev F F n a := by
  intro p q
  refine ⟨fun _ => Submodule.mem_top, fun hpq => ?_⟩
  rw [Submodule.mem_bot, Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl, rfl⟩ := hh
    exact absurd h hpq
  · rfl

theorem relMove {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    TwCoc (fun _ => 1) D.r D.G' z → D.KillsRel z i j →
      ∀ i' j' : Fin n, ((i : ℕ) < D.a ↔ (i' : ℕ) < D.a) → ((j : ℕ) < D.a ↔ (j' : ℕ) < D.a) → D.KillsRel z i' j' := by
  intro hz hk i' j' hi hj c hc h0
  have hA : Matrix.single i i' (1 : F) ∈ Submodule.span F (D.r '' D.G') := by
    rw [D.span]
    exact single_mem i i' hi
  have hB : Matrix.single j' j (1 : F) ∈ Submodule.span F (D.r '' D.G') := by
    rw [D.span]
    exact single_mem j' j hj.symm
  have hgen : ∀ A ∈ Submodule.span F (D.r '' D.G'), ∀ B ∈ Submodule.span F (D.r '' D.G'),
      (A * (c.sum fun g x => x • (z g * D.r g)) * B) i j = 0 := by
    intro A hA' B hB'
    induction hA' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      induction hB' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, hv, rfl⟩ := hy
        exact move_one D z i j hz hk c hc h0 hu hv
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [Matrix.mul_smul, Matrix.smul_apply, hx, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_apply, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, hx, smul_zero]
  have := hgen _ hA _ hB
  simpa [Matrix.mul_apply, Matrix.single_apply] using this

end UpperTheory.V.Pa.Det
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.RelPair
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.Det

section Quad

variable {F : Type} [Field F] {n m : ℕ}

private abbrev Quad (F : Type) (n m : ℕ) :=
  Matrix (Fin n) (Fin n) F × (Fin m → Matrix (Fin n) (Fin n) F) × (Fin m → Matrix (Fin n) (Fin n) F) ×
    Matrix (Fin n) (Fin n) F

end Quad

end UpperTheory.V.Pa.Det

theorem UpperTheory.V.Pa.Det.relPair :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ (c c' : G →₀ F), (∀ g ∈ c.support, g ∈ D.G') → (∀ g ∈ c'.support, g ∈ D.G') → c.sum (fun g x => x • D.r g) = 0 → c'.sum (fun g x => x • D.r g) = 0 → ∀ i j : Fin n, ¬ (((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)) → ∑ k, ((c.sum fun g x => x • (κ k g * D.r g)) i j * (c'.sum fun g x => x • (la k g * D.r g)) j i + (c.sum fun g x => x • (la k g * D.r g)) i j * (c'.sum fun g x => x • (κ k g * D.r g)) j i) = 0 := by
  intro F G _ _ n D m κ la s ph hK hT c c' hc hc' hRc hRc' i j _
  classical
  have hP : ∀ (g : G) (X : Matrix (Fin n) (Fin n) F), D.r g⁻¹ * (D.r g * X) = X := fun g X => by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hχ : ∀ g ∈ D.G', D.χF g = 1 := fun g hg => by simp [DetFr.χF, D.χ_triv g hg]
  have eK : ∀ k g h, κ k (g * h) = κ k g + D.r g * κ k h * D.r g⁻¹ := fun k g h => by
    have e := (hK.coc k) g (Set.mem_univ g) h (Set.mem_univ h)
    simpa using e
  have eL : ∀ g ∈ D.G', ∀ k h, la k (g * h) = la k g + D.r g * la k h * D.r g⁻¹ := fun g hg k h => by
    have e := (hT.coc k) g (Set.mem_univ g) h (Set.mem_univ h)
    rw [hχ g hg, one_smul] at e
    exact e
  have pK : ∀ k g h, κ k (g * h) * D.r (g * h) = κ k g * D.r g * D.r h + D.r g * (κ k h * D.r h) := by
    intro k g h
    rw [eK, map_mul]
    simp only [add_mul, mul_assoc, hP]
  have pL : ∀ g ∈ D.G', ∀ k h, la k (g * h) * D.r (g * h) = la k g * D.r g * D.r h + D.r g * (la k h * D.r h) := by
    intro g hg k h
    rw [eL g hg, map_mul]
    simp only [add_mul, mul_assoc, hP]
  have pQ : ∀ g ∈ D.G', ∀ h, ph (g * h) * D.r (g * h) + ∑ k, la k (g * h) * κ k (g * h) * D.r (g * h) =
      (ph g * D.r g + ∑ k, la k g * κ k g * D.r g) * D.r h + D.r g * (ph h * D.r h + ∑ k, la k h * κ k h * D.r h) +
      ∑ k, (κ k g * D.r g * (la k h * D.r h) + la k g * D.r g * (κ k h * D.r h)) := by
    intro g hg h
    have e := hT.ph_mul g h
    rw [hχ g hg, one_smul] at e
    rw [e, map_mul]
    simp only [eK, eL g hg]
    simp only [add_mul, mul_add, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc, hP]
    abel
  let pr : (G →₀ F) → (G →₀ F) → (G →₀ F) := fun c d =>
    c.sum fun g a => d.sum fun h b => Finsupp.single (g * h) (a * b)
  have gen : ∀ (v : G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F), Finsupp.linearCombination F v (pr c d) =
      c.sum fun g a => d.sum fun h b => (a * b) • v (g * h) := by
    intro v c d
    simp only [pr, map_finsuppSum, Finsupp.linearCombination_single]
  have lcMul : ∀ (v w : G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F),
      Finsupp.linearCombination F v c * Finsupp.linearCombination F w d =
      c.sum fun g a => d.sum fun h b => (a * b) • (v g * w h) := by
    intro v w c d
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mul]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [smul_mul_smul_comm]
  have dK : ∀ (W : Fin m → G → G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F),
      (∑ k, c.sum fun g a => d.sum fun h b => (a * b) • W k g h) =
      c.sum fun g a => d.sum fun h b => (a * b) • ∑ k, W k g h := by
    intro W c d
    simp only [Finsupp.sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
  have memS : ∀ (p : G →₀ F), p ∈ Finsupp.supported F F (D.G' : Set G) → ∀ g ∈ p.support, g ∈ D.G' :=
    fun p hp g hg => (Finsupp.mem_supported F p).1 hp (Finset.mem_coe.2 hg)
  have prS : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ d ∈ Finsupp.supported F F (D.G' : Set G),
      pr c d ∈ Finsupp.supported F F (D.G' : Set G) := by
    intro c hc d hd
    refine Submodule.finsuppSum_mem F _ c _ fun g hg => Submodule.finsuppSum_mem F _ d _ fun h hh => ?_
    exact Finsupp.single_mem_supported F _ (D.G'.mul_mem (memS c hc g (Finsupp.mem_support_iff.2 hg))
      (memS d hd h (Finsupp.mem_support_iff.2 hh)))
  have mR : ∀ c d, Finsupp.linearCombination F D.r (pr c d) =
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F D.r d := by
    intro c d
    rw [gen, lcMul]
    simp only [map_mul]
  have mK : ∀ k, ∀ c d, Finsupp.linearCombination F (fun g => κ k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => κ k g * D.r g) c * Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F (fun g => κ k g * D.r g) d := by
    intro k c d
    rw [gen, lcMul, lcMul, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [pK, smul_add]
  have mL : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ k d,
      Finsupp.linearCombination F (fun g => la k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => la k g * D.r g) c * Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F (fun g => la k g * D.r g) d := by
    intro c hc k d
    rw [gen, lcMul, lcMul, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g hg => ?_
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [pL g (memS c hc g hg), smul_add]
  have mQ : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ d,
      Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) c *
        Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c *
        Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) d +
      ∑ k, (Finsupp.linearCombination F (fun g => κ k g * D.r g) c *
          Finsupp.linearCombination F (fun g => la k g * D.r g) d +
        Finsupp.linearCombination F (fun g => la k g * D.r g) c *
          Finsupp.linearCombination F (fun g => κ k g * D.r g) d) := by
    intro c hc d
    have hs : (∑ k, (Finsupp.linearCombination F (fun g => κ k g * D.r g) c *
          Finsupp.linearCombination F (fun g => la k g * D.r g) d +
        Finsupp.linearCombination F (fun g => la k g * D.r g) c *
          Finsupp.linearCombination F (fun g => κ k g * D.r g) d)) =
        c.sum fun g a => d.sum fun h b => (a * b) •
          ∑ k, (κ k g * D.r g * (la k h * D.r h) + la k g * D.r g * (κ k h * D.r h)) := by
      refine Eq.trans ?_ (dK _ c d)
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [lcMul, lcMul, ← Finsupp.sum_add]
      refine Finsupp.sum_congr fun g _ => ?_
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun h _ => ?_
      rw [smul_add]
    rw [gen, hs, lcMul, lcMul, ← Finsupp.sum_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g hg => ?_
    rw [← Finsupp.sum_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [← smul_add, ← smul_add, pQ g (memS c hc g hg) h]
  have trQ : ∀ p ∈ Finsupp.supported F F (D.G' : Set G),
      (Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) p).trace = 0 := by
    intro p hp
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun g hg => ?_
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sum, hT.ell g (memS p hp g hg), smul_zero]
  have hEv : ∀ t : Fin n, Matrix.single t t (1 : F) ∈ Submodule.span F (D.r '' (D.G' : Set G)) := by
    intro t
    rw [D.span]
    intro i' j'
    refine ⟨fun _ => trivial, fun h => ?_⟩
    rw [Submodule.mem_bot, Matrix.single_apply]
    split_ifs with e
    · obtain ⟨rfl, rfl⟩ := e
      exact absurd Iff.rfl h
    · rfl
  have hS : c ∈ Finsupp.supported F F (D.G' : Set G) :=
    (Finsupp.mem_supported F c).2 fun g hg => hc g (Finset.mem_coe.1 hg)
  have hS' : c' ∈ Finsupp.supported F F (D.G' : Set G) :=
    (Finsupp.mem_supported F c').2 fun g hg => hc' g (Finset.mem_coe.1 hg)
  obtain ⟨dj, hdj, hj⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 (hEv j)
  obtain ⟨di, hdi, hi⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 (hEv i)
  have hR0 : Finsupp.linearCombination F D.r c = 0 := by
    rw [Finsupp.linearCombination_apply]; exact hRc
  have hR0' : Finsupp.linearCombination F D.r c' = 0 := by
    rw [Finsupp.linearCombination_apply]; exact hRc'
  have tr : ∀ A B : Matrix (Fin n) (Fin n) F,
      (A * Matrix.single j j 1 * (B * Matrix.single i i 1)).trace = A i j * B j i := by
    intro A B
    rw [← mul_assoc, Matrix.trace_mul_single]
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
  have key := trQ _ (prS _ (prS c hS dj hdj) _ (prS c' hS' di hdi))
  rw [mQ _ (prS c hS dj hdj)] at key
  simp only [mR, mK, mL c hS, mL c' hS', hR0, hR0', hi, hj, zero_mul, mul_zero, add_zero, zero_add] at key
  rw [Matrix.trace_sum] at key
  simp only [Matrix.trace_add, tr] at key
  simpa only [Finsupp.linearCombination_apply] using key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ResExt
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem map_finite {K L : Type} [Field K] [Field L] [Finite L] (f : K →+* L) :
    (PowerSeries.map f).Finite := by
  classical
  letI := f.toAlgebra
  letI := (PowerSeries.map f).toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_finite
  let b := Module.finBasis K L
  show Module.Finite (PowerSeries K) (PowerSeries L)
  refine ⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩
  rw [eq_top_iff]
  intro φ _
  have key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) •
      PowerSeries.C (b i) := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (b.sum_repr _).symm.trans (Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _)
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

private theorem bijective_residue_comp_powerSeries_C (F : Type) [Field F] :
    Function.Bijective ((residue (PowerSeries F)).comp (PowerSeries.C (R := F))) := by
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y
  refine ⟨PowerSeries.constantCoeff x, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C,
    sub_self]
  exact not_isUnit_zero

theorem UpperTheory.V.Pa.Det.resExt :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] (d D : ℕ), Nat.card K = l ^ d → d ∣ D → D ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ Nat.card (ResidueField A') = l ^ D ∧ Irreducible (j PowerSeries.X) := by
  intro l _ K _ _ _ d D hK hdD hD
  have hd : d ≠ 0 := by
    rintro rfl
    exact hD (zero_dvd_iff.mp hdD)
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  let e := GaloisField.algEquivGaloisField l d hK
  obtain ⟨g⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod l)
    (K := GaloisField l d) (L := GaloisField l D)
    (by rw [GaloisField.finrank l hd, GaloisField.finrank l hD]; exact hdD)
  let φ : K →+* GaloisField l D := (g.comp e.toAlgHom).toRingHom
  have hcc : ∀ ψ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map φ ψ) =
      φ (PowerSeries.constantCoeff ψ) := by
    intro ψ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  haveI : CharP (PowerSeries (GaloisField l D)) l :=
    charP_of_injective_ringHom (PowerSeries.C (R := GaloisField l D)).injective l
  haveI : UpperTheory.V.Pa.IsEqDVR l (PowerSeries (GaloisField l D)) :=
    ⟨by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      Finite.of_surjective _ (bijective_residue_comp_powerSeries_C (GaloisField l D)).2, inferInstance⟩
  refine ⟨PowerSeries (GaloisField l D), inferInstance, inferInstance, inferInstance, inferInstance,
    PowerSeries.map φ, PowerSeries.map_injective _ φ.injective, ⟨fun ψ hψ => ?_⟩,
    map_finite φ, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero,
      map_ne_zero_iff _ φ.injective] at hψ
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hψ
  · rw [← Nat.card_congr (Equiv.ofBijective _ (bijective_residue_comp_powerSeries_C (GaloisField l D))),
      GaloisField.card l D hD]
  · rw [PowerSeries.map_X]
    exact PowerSeries.X_irreducible
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanInt
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image {A F M N : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M) (y : N)
    (hy : y ∈ Submodule.span F (φ '' T)) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A T, d • y = φ w :=
  _root_.UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image φ T y hy

theorem UpperTheory.V.Pa.Det.spanInt :
    ∀ {K ι : Type} [Field K] {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) (PowerSeries K)) (S : Set ι), Submodule.span (FractionRing (PowerSeries K)) ((fun i => (r i).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) '' S) = Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a → ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ, (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) (r '' S) := by
  intro K ι _ n a r S h Z hZ
  let φ : Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[PowerSeries K]
      Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K)) :=
    (Algebra.linearMap (PowerSeries K) (FractionRing (PowerSeries K))).mapMatrix
  have hφ : ∀ Y, φ Y = Y.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) := fun _ => rfl
  have hinj : Function.Injective φ :=
    Matrix.map_injective (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hmem : φ Z ∈ Submodule.span (FractionRing (PowerSeries K)) (φ '' (r '' S)) := by
    rw [Set.image_image]
    simp only [hφ]
    rw [h]
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
    have : Z i j = 0 := (Submodule.mem_bot _).1 ((hZ i j).2 hij)
    simp [this]
  obtain ⟨d, hd, w, hw, e⟩ := UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image φ _ _ hmem
  rw [← map_smul] at e
  have e' := hinj e
  obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd
    (PowerSeries.X_irreducible (R := K))
  refine ⟨s, ?_⟩
  have : (PowerSeries.X : PowerSeries K) ^ s • Z = (↑u⁻¹ : PowerSeries K) • w := by
    rw [← e', smul_smul, Units.inv_mul_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ hw
end

