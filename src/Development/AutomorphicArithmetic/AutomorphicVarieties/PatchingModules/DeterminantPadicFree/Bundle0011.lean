module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.AcConst
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ac_mul {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} {f h : G → R}
    (hf : AdicCont I f) (hh : AdicCont I h) : AdicCont I fun g => f g * h g := fun N => by
  simp only [map_mul]; exact (hf N).mul (hh N)

private theorem ac_const {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (c : R) :
    AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

private theorem ac_sum {G R ι : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (s : Finset ι)
    {f : ι → G → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := by
  classical
  intro N
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a N).add ih

private theorem mat_lc {G A R : Type} [TopologicalSpace G] [CommRing A] [CommRing R] [Algebra A R]
    {n : ℕ} (t : A) (f : G → Matrix (Fin n) (Fin n) R)
    (hf : ∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => f g i j) (N : ℕ) :
    IsLocallyConstant fun g =>
      (Ideal.span {t} ^ N • (⊤ : Submodule A (Matrix (Fin n) (Fin n) R))).mkQ (f g) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : ∀ᶠ y in nhds x, ∀ i j, Ideal.Quotient.mk (Ideal.span {algebraMap A R t} ^ N) (f y i j)
      = Ideal.Quotient.mk (Ideal.span {algebraMap A R t} ^ N) (f x i j) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hf i j N).eventually_eq x
  filter_upwards [hx] with y hy
  have hc : ∀ i j, ∃ c : R, c * algebraMap A R t ^ N = f y i j - f x i j := by
    intro i j
    have h := Ideal.Quotient.eq.1 (hy i j)
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  choose c hc using hc
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  have hm : f y - f x = t ^ N • Matrix.of c := by
    ext i j
    simp [Algebra.smul_def, ← hc i j, mul_comm]
  rw [hm, Ideal.span_singleton_pow]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem UpperTheory.V.Pa.Det.matFg :
    ∀ (l : ℕ) [Fact l.Prime] {K G R : Type} [Field K] [Finite K] [CharP K l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [CommRing R] [Algebra (PowerSeries K) R] [Module.Free (PowerSeries K) R] [Module.Finite (PowerSeries K) R] {n : ℕ} (χ : G →* R) (r : G →* Matrix (Fin n) (Fin n) R) (Z : Submodule (PowerSeries K) (G → Matrix (Fin n) (Fin n) R)), PhiCond G l → AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) χ → (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => r g i j) → (∀ z ∈ Z, (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => z g i j) ∧ TwCoc χ r Set.univ z) → Z.FG := by
  intro l _ K G R _ _ _ _ _ _ _ _ _ _ _ _ n χ r Z hφ hχ hr hZ
  let ρ : G →* Module.End (PowerSeries K) (Matrix (Fin n) (Fin n) R) :=
    { toFun := fun g =>
        { toFun := fun m => χ g • (r g * m * r g⁻¹)
          map_add' := by intro a b; simp [Matrix.mul_add, Matrix.add_mul]
          map_smul' := by
            intro c m
            simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
            exact smul_comm _ _ _ }
      map_one' := by ext m : 1; simp
      map_mul' := by
        intro g h
        ext m : 1
        simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm] }
  have hinv : ∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => r g⁻¹ i j :=
    fun i j N => (hr i j N).comp_continuous continuous_inv
  refine Det.z1Fg l ρ Z hφ ?_ ?_
  · intro N m
    refine mat_lc PowerSeries.X (fun g => χ g • (r g * m * r g⁻¹)) ?_ N
    intro i j
    have e : (fun g => (χ g • (r g * m * r g⁻¹)) i j)
        = fun g => χ g * ∑ q, (∑ k, r g i k * m k q) * r g⁻¹ q j := by
      funext g
      simp [Matrix.mul_apply]
    rw [e]
    exact ac_mul hχ (ac_sum _ fun q => ac_mul (ac_sum _ fun k => ac_mul (hr i k) (ac_const _)) (hinv q j))
  · intro z hz
    obtain ⟨hzc, hzt⟩ := hZ z hz
    exact ⟨fun N => mat_lc PowerSeries.X z hzc N, fun g h => hzt g trivial h trivial⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.BlockPrinc
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem coc_comb {F G : Type} [Field F] [Group G] {n m : ℕ} (χ : G → F)
    (r : G → Matrix (Fin n) (Fin n) F) (z : Fin m → G → Matrix (Fin n) (Fin n) F) (α : Fin m → F)
    (hz : ∀ k, TwCoc χ r Set.univ (z k)) : TwCoc χ r Set.univ fun g => ∑ k, α k • z k g := by
  intro g _ h _
  show ∑ k, α k • z k (g * h) = ∑ k, α k • z k g + χ g • (r g * (∑ k, α k • z k h) * r g⁻¹)
  rw [Finset.sum_congr rfl fun k _ => by rw [hz k g (Set.mem_univ _) h (Set.mem_univ _)]]
  simp [smul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]

private theorem cut_mul {F : Type} [Field F] {n : ℕ} (p q : Fin n → Prop) [∀ i j, Decidable (p i ∧ q j)]
    (Z B : Matrix (Fin n) (Fin n) F) (hB : ∀ k j, ¬ (q k ↔ q j) → B k j = 0) (i j : Fin n) :
    ((Matrix.of fun i j => if p i ∧ q j then Z i j else 0) * B) i j = if p i ∧ q j then (Z * B) i j else 0 := by
  simp only [Matrix.mul_apply, Matrix.of_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : q k ↔ q j
    · rw [if_pos ⟨h.1, hk.2 h.2⟩]
    · rw [hB k j hk, mul_zero, mul_zero]
  · refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : q k ↔ q j
    · rw [if_neg (fun h' => h ⟨h'.1, hk.1 h'.2⟩), zero_mul]
    · rw [hB k j hk, mul_zero]

private theorem kills_cut {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (p q : Fin n → Prop) [∀ i j, Decidable (p i ∧ q j)] (z : G → Matrix (Fin n) (Fin n) F)
    (hq : ∀ k j, ¬ (q k ↔ q j) → ¬ ((k : ℕ) < D.a ↔ (j : ℕ) < D.a))
    (hk : ∀ i j, p i → q j → D.KillsRel z i j) (i j : Fin n) :
    D.KillsRel (fun g => Matrix.of fun i j => if p i ∧ q j then z g i j else 0) i j := by
  intro c hc hs
  have hev : ∀ g k l, ¬ (q k ↔ q l) → D.r g k l = 0 := by
    intro g k l h
    exact (Submodule.mem_bot F).1 (((D.ev g) k l).2 (hq k l h))
  have e : ∀ g, ((Matrix.of fun i j => if p i ∧ q j then z g i j else 0) * D.r g) i j
      = if p i ∧ q j then (z g * D.r g) i j else 0 := fun g => cut_mul p q (z g) (D.r g) (hev g) i j
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, e]
  split_ifs with h
  · have := hk i j h.1 h.2 c hc hs
    simpa [Finsupp.sum, Matrix.sum_apply] using this
  · simp

private theorem block_princ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (K L : G → Matrix (Fin n) (Fin n) F) (hK : TwCoc (fun _ => 1) D.r Set.univ K)
    (hL : TwCoc D.χF D.r Set.univ L) (hKo : ∀ g, K g ∈ Od F F n D.a) (hLo : ∀ g, L g ∈ Od F F n D.a)
    (hk : ∀ i j, D.KillsRel (fun g => K g + L g) i j) :
    (∃ Y, ∀ g, K g = dTw (fun _ => 1) D.r Y g) ∧ ∃ Y, ∀ g, L g = dTw D.χF D.r Y g := by
  have hKL : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g) := by
    intro g hg h _
    have e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹ := by simpa using hK g trivial h trivial
    have e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹ := by
      simpa [DetFr.χF, D.χ_triv g hg] using hL g trivial h trivial
    show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)
    rw [e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  obtain ⟨Y, hY⟩ := Det.der D _ hKL hk
  obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := Det.eigen D K L Y hK hL hY
  have hχ1 : ∀ g ∈ D.G', D.χF g = 1 := by intro g hg; simp [DetFr.χF, D.χ_triv g hg]
  have hY2' : ∀ g ∈ D.G', L g = dTw D.χF D.r Y2 g := by
    intro g hg
    rw [hY2 g hg]
    simp [dTw, hχ1 g hg]
  obtain ⟨Z1, -, hZ1⟩ := Det.infres D (fun _ => 1) K Y1 (by intros; simp) (by intros; rfl) hK hKo hY1
  obtain ⟨Z2, -, hZ2⟩ := Det.infres D D.χF L Y2 (by intro g h; simp [DetFr.χF]) hχ1 hL hLo hY2'
  exact ⟨⟨Z1, hZ1⟩, ⟨Z2, hZ2⟩⟩

theorem UpperTheory.V.Pa.Det.ann :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ (α β : Fin m → F) (i j : Fin n), ¬ (((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)) → D.KillsRel (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) i j → α = 0 ∧ ∃ Y ∈ Od F F n D.a, s • Yᵀ = Y ∧ ∀ g, ∑ k, β k • la k g = dTw D.χF D.r Y g := by
  classical
  intro F G _ _ n D m κ la s ph hκ hla α β i j hij hkill
  obtain ⟨K, hKe⟩ : ∃ K : G → Matrix (Fin n) (Fin n) F, K = fun g => ∑ k, α k • κ k g := ⟨_, rfl⟩
  obtain ⟨L, hLe⟩ : ∃ L : G → Matrix (Fin n) (Fin n) F, L = fun g => ∑ k, β k • la k g := ⟨_, rfl⟩
  rw [show (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) = fun g => K g + L g by rw [hKe, hLe]] at hkill
  have hKc : TwCoc (fun _ => (1 : F)) D.r Set.univ K := by rw [hKe]; exact coc_comb _ _ κ α hκ.coc
  have hLc : TwCoc D.χF D.r Set.univ L := by rw [hLe]; exact coc_comb _ _ la β hla.coc
  have hKo : ∀ g, K g ∈ Od F F n D.a := fun g => by
    rw [hKe]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hκ.od k g)
  have hLo : ∀ g, L g ∈ Od F F n D.a := fun g => by
    rw [hLe]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hla.od k g)
  have hKp : ∀ g, K (D.σ g) = (-1 : F) • (K g)ᵀ := by
    intro g; rw [hKe]; simp [hκ.pol, Matrix.transpose_sum]
  have hLp : ∀ g, L (D.σ g) = s • (L g)ᵀ := by
    intro g; rw [hLe]; simp [hla.pol, Matrix.transpose_sum, Finset.smul_sum, smul_smul, mul_comm]
  have hTot : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g) := by
    intro g hg h _
    have e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹ := by simpa using hKc g trivial h trivial
    have e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹ := by
      simpa [DetFr.χF, D.χ_triv g hg] using hLc g trivial h trivial
    show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)
    rw [e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  obtain ⟨p, hpd⟩ : ∃ p : Fin n → Prop, ∀ x, p x ↔ ((x : ℕ) < D.a ↔ (i : ℕ) < D.a) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q : Fin n → Prop, ∀ x, q x ↔ ((x : ℕ) < D.a ↔ (j : ℕ) < D.a) := ⟨_, fun _ => Iff.rfl⟩
  have hq : ∀ k l, ¬ (q k ↔ q l) → ¬ ((k : ℕ) < D.a ↔ (l : ℕ) < D.a) := by
    intro k l h h'
    apply h
    rw [hqd k, hqd l]
    tauto
  have hk' : ∀ i' j', p i' → q j' → D.KillsRel (fun g => K g + L g) i' j' := fun i' j' hi' hj' =>
    Det.relMove D _ i j hTot hkill i' j' ((hpd i').1 hi').symm ((hqd j').1 hj').symm
  have cK := Det.cornerCoc D _ _ _ hKc
  have cL := Det.cornerCoc D _ _ _ hLc
  have hcase : ((i : ℕ) < D.a ∧ ¬ (j : ℕ) < D.a) ∨ (¬ (i : ℕ) < D.a ∧ (j : ℕ) < D.a) := by tauto
  have key : ∃ Y1 Y2, ((∀ g, cV D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g) ∨
      (∀ g, cV' D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g)) ∧
      ((∀ g, cV D.a (L g) = dTw D.χF D.r Y2 g) ∨ (∀ g, cV' D.a (L g) = dTw D.χF D.r Y2 g)) := by
    rcases hcase with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hc2 : ∀ i' j', D.KillsRel (fun g => cV D.a (K g) + cV D.a (L g)) i' j' := by
        intro i' j'
        rw [show (fun g => cV D.a (K g) + cV D.a (L g)) =
            fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by
          funext g
          ext a b
          have hpa : p a ↔ (a : ℕ) < D.a := by rw [hpd]; tauto
          have hqb : q b ↔ ¬ (b : ℕ) < D.a := by rw [hqd]; tauto
          simp only [cV, Matrix.of_apply, Matrix.add_apply]
          split_ifs <;> first | rfl | (exfalso; tauto) | simp]
        exact kills_cut D p q (fun g => K g + L g) hq hk' i' j'
      obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := block_princ D (fun g => cV D.a (K g)) (fun g => cV D.a (L g))
        cK.1 cL.1 (fun g => (cK.2.2.2 (K g)).1) (fun g => (cL.2.2.2 (L g)).1) hc2
      exact ⟨Y1, Y2, Or.inl hY1, Or.inl hY2⟩
    · have hc2 : ∀ i' j', D.KillsRel (fun g => cV' D.a (K g) + cV' D.a (L g)) i' j' := by
        intro i' j'
        rw [show (fun g => cV' D.a (K g) + cV' D.a (L g)) =
            fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by
          funext g
          ext a b
          have hpa : p a ↔ ¬ (a : ℕ) < D.a := by rw [hpd]; tauto
          have hqb : q b ↔ (b : ℕ) < D.a := by rw [hqd]; tauto
          simp only [cV', Matrix.of_apply, Matrix.add_apply]
          split_ifs <;> first | rfl | (exfalso; tauto) | simp]
        exact kills_cut D p q (fun g => K g + L g) hq hk' i' j'
      obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := block_princ D (fun g => cV' D.a (K g)) (fun g => cV' D.a (L g))
        cK.2.1 cL.2.1 (fun g => (cK.2.2.2 (K g)).2.1) (fun g => (cL.2.2.2 (L g)).2.1) hc2
      exact ⟨Y1, Y2, Or.inr hY1, Or.inr hY2⟩
  obtain ⟨Y1, Y2, hK1, hL2⟩ := key
  obtain ⟨YK, hYKo, hYKs, hYK⟩ :=
    Det.shapiro D (fun _ => (1 : F)) (-1) K Y1 (fun _ => rfl) (by norm_num) hKc hKo hKp hK1
  obtain ⟨YL, hYLo, hYLs, hYL⟩ :=
    Det.shapiro D D.χF s L Y2 (fun g => by simp [DetFr.χF, D.χσ]) hla.sq hLc hLo hLp hL2
  have hT : YKᵀ = -YK := by
    have h := congrArg Matrix.transpose hYKs
    simp only [Matrix.transpose_smul, Matrix.transpose_transpose, neg_smul, one_smul] at h
    exact h.symm
  have hα : α = 0 := hκ.indep α YK hYKo hT fun g => by
    have := hYK g
    rw [hKe] at this
    exact this
  exact ⟨hα, YL, hYLo, hYLs, fun g => by
    have := hYL g
    rw [hLe] at this
    exact this⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CharPOfPadicAlt
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpr : p.Prime := CharP.char_is_prime K p
  by_cases h : p = l
  · subst h
    exact hp
  · exfalso
    have hu : IsUnit (p : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out hpr).2 (Ne.symm h)
    have hu' := hu.map f
    rw [map_natCast, CharP.cast_eq_zero] at hu'
    exact not_isUnit_zero hu'

theorem UpperTheory.V.Pa.Det.onePt :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) {q : ℕ} (sg : Fin q → F.G₀), (∀ a, ((mat x.ρ (sg a)).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable) → Detects k (Set.range sg) → ∃ d : ℕ, d ≠ 0 ∧ ∀ D, d ∣ D → D ≠ 0 → ∃ (x' : NP F n) (j : x.A →+* x'.A) (k' : Kap x') (al : Fin q → Fin n → x'.A), x.Ext x' j ∧ Nat.card x'.K = l ^ D ∧ Detects k' (Set.range sg) ∧ ∀ a, Function.Injective (al a) ∧ (mat x'.ρ (sg a)).charpoly = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ F n x k q sg hsep hdet
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  have hmat : ∀ (y y' : NP F n) (j : y.A →+* y'.A), y.Ext y' j → ∀ g, mat y'.ρ g = (mat y.ρ g).map j := by
    intro y y' j h g
    rw [h.2.2.2.1]
    rfl
  obtain ⟨A1, _, _, _, _, j1, al1, hj1i, hj1l, hj1f, hal1⟩ :=
    Det.splitEx l (n := n) (fun a => (mat x.ρ (sg a)).charpoly)
      (fun a => ⟨Matrix.charpoly_monic _, by simp [Matrix.charpoly_natDegree_eq_dim], hsep a⟩)
  obtain ⟨x1, J1, e1, hE1, he1, -⟩ := Det.extEx x A1 j1 hj1i hj1l hj1f
  haveI : CharP x1.K l := charP_of_padic (algebraMap ℤ_[l] x1.K)
  haveI := Fintype.ofFinite x1.K
  obtain ⟨d, -, hcard⟩ := FiniteField.card x1.K l
  refine ⟨(d : ℕ), d.ne_zero, ?_⟩
  intro D hdD hD0
  obtain ⟨A2, _, _, _, _, j2, hj2i, hj2l, hj2f, hres2, -⟩ :=
    Det.resExt l (K := x1.K) d D (by rw [Nat.card_eq_fintype_card]; exact hcard) hdD hD0
  obtain ⟨x2, J2, e2, hE2, -, hc2⟩ := Det.extEx x1 A2 j2 hj2i hj2l hj2f
  have hE := Det.extTrans x x1 x2 J1 J2 hE1 hE2
  obtain ⟨k', e, hk, -⟩ := Det.kapPush x x2 _ hE k
  refine ⟨x2, J2.comp J1, k', fun a b => J2 (e1.symm (al1 a b)), hE.1, by rw [hc2, hres2],
    Det.detPush x x2 _ hE k k' e hk _ hdet, fun a => ⟨?_, ?_⟩⟩
  · exact hE2.1.1.comp (e1.symm.injective.comp (hal1 a).1)
  · have h1 : J1 = (e1.symm : A1 →+* x1.A).comp j1 := by
      refine RingHom.ext fun t => ?_
      simp [← he1 t]
    have key : Polynomial.map J1 (mat x.ρ (sg a)).charpoly =
        ∏ b, (Polynomial.X - Polynomial.C (e1.symm (al1 a b))) := by
      rw [h1, ← Polynomial.map_map, (hal1 a).2, Polynomial.map_prod]
      simp
    rw [hmat x x2 _ hE.1, Matrix.charpoly_map, ← Polynomial.map_map, key, Polynomial.map_prod]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TwoBlock
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Blocks

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private def bd (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    Matrix (Fin (a + b)) (Fin (a + b)) R :=
  (fromBlocks A 0 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

private theorem bd_mul (A A' : Matrix (Fin a) (Fin a) R) (D D' : Matrix (Fin b) (Fin b) R) :
    bd A D * bd A' D' = bd (A * A') (D * D') := by
  simp [bd, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem bd_one : bd (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  simp [bd]

private theorem bd_transpose (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D)ᵀ = bd Aᵀ Dᵀ := by
  simp [bd, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

private theorem bd_map (f : R →+* S) (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D).map f = bd (A.map f) (D.map f) := by
  unfold bd
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

private theorem bd_smul (c : R) (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    c • bd A D = bd (c • A) (c • D) := by
  unfold bd
  ext i j
  simp only [Matrix.smul_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = x
  generalize finSumFinEquiv.symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp

private theorem bd_ll (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    bd A D (Fin.castAdd b i) (Fin.castAdd b j) = A i j := by
  simp [bd]

private theorem bd_rr (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    bd A D (Fin.natAdd a i) (Fin.natAdd a j) = D i j := by
  simp [bd]

private theorem bd_inj {A A' : Matrix (Fin a) (Fin a) R} {D D' : Matrix (Fin b) (Fin b) R}
    (h : bd A D = bd A' D') : A = A' ∧ D = D' := by
  constructor
  · ext i j; rw [← bd_ll A D, h, bd_ll]
  · ext i j; rw [← bd_rr A D, h, bd_rr]

private theorem bd_det (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D).det = A.det * D.det := by
  simp [bd]

private theorem bd_mem (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    bd A D ∈ Ev R R (a + b) a := by
  intro i j
  refine ⟨fun _ => trivial, fun h => ?_⟩
  rw [Submodule.mem_bot]
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [bd] at h ⊢

private theorem bd_ex {M : Matrix (Fin (a + b)) (Fin (a + b)) R} (h : M ∈ Ev R R (a + b) a) :
    ∃ A D, M = bd A D := by
  refine ⟨M.submatrix (Fin.castAdd b) (Fin.castAdd b), M.submatrix (Fin.natAdd a) (Fin.natAdd a), ?_⟩
  ext i j
  have h' := (h i j).2
  rw [Submodule.mem_bot] at h'
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [bd] at h' ⊢ <;> exact h'

private def bdU (A : GL (Fin a) R) (D : GL (Fin b) R) : GL (Fin (a + b)) R :=
  ⟨bd A.val D.val, bd A⁻¹.val D⁻¹.val, by rw [bd_mul, Units.mul_inv, Units.mul_inv, bd_one],
    by rw [bd_mul, Units.inv_mul, Units.inv_mul, bd_one]⟩

private def bdRep {G : Type} [Group G] (r₁ : G →* GL (Fin a) R) (r₂ : G →* GL (Fin b) R) :
    G →* GL (Fin (a + b)) R where
  toFun g := bdU (r₁ g) (r₂ g)
  map_one' := Units.ext (by
    show bd (r₁ 1).val (r₂ 1).val = 1
    rw [map_one, map_one, Units.val_one, Units.val_one, bd_one])
  map_mul' g h := Units.ext (by
    show bd (r₁ (g * h)).val (r₂ (g * h)).val = bd (r₁ g).val (r₂ g).val * bd (r₁ h).val (r₂ h).val
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, bd_mul])

private theorem rep_ex {G : Type} [Group G] (r : G →* GL (Fin (a + b)) R)
    (h : ∀ g, mat r g ∈ Ev R R (a + b) a) :
    ∃ (r₁ : G →* GL (Fin a) R) (r₂ : G →* GL (Fin b) R), ∀ g, (r g).val = bd (r₁ g).val (r₂ g).val := by
  choose A D hAD using fun g => bd_ex (h g)
  have h1 : bd (A 1) (D 1) = bd 1 1 := by rw [← hAD, map_one, bd_one]
  have hm : ∀ g g', bd (A (g * g')) (D (g * g')) = bd (A g * A g') (D g * D g') := fun g g' => by
    rw [← bd_mul, ← hAD, ← hAD, ← hAD, map_mul]
  let A' : G →* Matrix (Fin a) (Fin a) R := ⟨⟨A, (bd_inj h1).1⟩, fun g g' => (bd_inj (hm g g')).1⟩
  let D' : G →* Matrix (Fin b) (Fin b) R := ⟨⟨D, (bd_inj h1).2⟩, fun g g' => (bd_inj (hm g g')).2⟩
  exact ⟨A'.toHomUnits, D'.toHomUnits, fun g => hAD g⟩

end Blocks

theorem UpperTheory.V.Pa.Det.twoBlock :
    ∀ {K K' G : Type} [Field K] [Field K'] [Group G] {n : ℕ} (a : ℕ) (j₁ : PowerSeries K →+* PowerSeries K) (f₁ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K)) (j₂ : PowerSeries K →+* PowerSeries K') (f₂ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K')) (r : G →* GL (Fin n) (FractionRing (PowerSeries K))) (H : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K))) (σ : G → G) (u : G → PowerSeries K) (d : PowerSeries K), (2 : K) ≠ 0 → (∀ y, f₁ (algebraMap _ _ y) = algebraMap _ _ (j₁ y)) → (∀ y, f₂ (algebraMap _ _ y) = algebraMap _ _ (j₂ y)) → j₁ PowerSeries.X = PowerSeries.X ^ 2 → (∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j₂ c))) → d ≠ 0 → (∀ g i i', ∃ y : PowerSeries K, algebraMap _ (FractionRing (PowerSeries K)) d * r g i i' = algebraMap _ (FractionRing (PowerSeries K)) y) → Hᵀ = H → H.det ≠ 0 → Function.Surjective σ → (∀ g, (mat r g)ᵀ * H * mat r (σ g) = algebraMap _ (FractionRing (PowerSeries K)) (u g) • H) → a ≤ n → (∀ g, mat r g ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a) → H ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a → ∃ (Q : GL (Fin n) (FractionRing (PowerSeries K'))) (r' : G →* GL (Fin n) (PowerSeries K')), (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K')))ᵀ * H.map (f₂.comp f₁) * Q = 1 ∧ (∀ g, pushRep (f₂.comp f₁) r g * Q = Q * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) r' g) ∧ (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) ∈ Ev (FractionRing (PowerSeries K')) (FractionRing (PowerSeries K')) n a ∧ ∀ g, mat r' g ∈ Ev (PowerSeries K') (PowerSeries K') n a := by
  intro K K' G _ _ _ n a j₁ f₁ j₂ f₂ r H σ u d h2 hf₁ hf₂ hX hsq hd hb hH hdet hσ hr ha hev hHev
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨H₁, H₂, rfl⟩ := bd_ex hHev
  obtain ⟨r₁, r₂, hrr⟩ := rep_ex r hev
  rw [bd_transpose] at hH
  rw [bd_det] at hdet
  have hr' : ∀ g, bd ((mat r₁ g)ᵀ * H₁ * mat r₁ (σ g)) ((mat r₂ g)ᵀ * H₂ * mat r₂ (σ g)) =
      bd (algebraMap _ (FractionRing (PowerSeries K)) (u g) • H₁)
        (algebraMap _ (FractionRing (PowerSeries K)) (u g) • H₂) := fun g => by
    rw [← bd_smul, ← hr g, ← bd_mul, ← bd_mul, ← bd_transpose]
    show _ = ((r g).val)ᵀ * _ * (r (σ g)).val
    rw [hrr, hrr]
    rfl
  obtain ⟨Q₁, s₁, hQ₁, hs₁⟩ := UpperTheory.V.Pa.Det.oneBlock j₁ f₁ j₂ f₂ r₁ H₁ σ u d h2 hf₁ hf₂ hX hsq hd
    (fun g i i' => by
      obtain ⟨y, hy⟩ := hb g (Fin.castAdd b i) (Fin.castAdd b i')
      refine ⟨y, ?_⟩
      rw [← hy]
      show _ * (r₁ g).val i i' = _ * (r g).val _ _
      rw [hrr, bd_ll])
    (bd_inj hH).1 (left_ne_zero_of_mul hdet) hσ (fun g => (bd_inj (hr' g)).1)
  obtain ⟨Q₂, s₂, hQ₂, hs₂⟩ := UpperTheory.V.Pa.Det.oneBlock j₁ f₁ j₂ f₂ r₂ H₂ σ u d h2 hf₁ hf₂ hX hsq hd
    (fun g i i' => by
      obtain ⟨y, hy⟩ := hb g (Fin.natAdd a i) (Fin.natAdd a i')
      refine ⟨y, ?_⟩
      rw [← hy]
      show _ * (r₂ g).val i i' = _ * (r g).val _ _
      rw [hrr, bd_rr])
    (bd_inj hH).2 (right_ne_zero_of_mul hdet) hσ (fun g => (bd_inj (hr' g)).2)
  refine ⟨bdU Q₁ Q₂, bdRep s₁ s₂, ?_, fun g => Units.ext ?_, bd_mem _ _, fun g => bd_mem _ _⟩
  · show (bd Q₁.val Q₂.val)ᵀ * _ * bd Q₁.val Q₂.val = 1
    rw [bd_map, bd_transpose, bd_mul, bd_mul, hQ₁, hQ₂, bd_one]
  · have e₁ : (r₁ g).val.map (f₂.comp f₁) * Q₁.val = Q₁.val * (s₁ g).val.map (algebraMap _ _) :=
      congrArg Units.val (hs₁ g)
    have e₂ : (r₂ g).val.map (f₂.comp f₁) * Q₂.val = Q₂.val * (s₂ g).val.map (algebraMap _ _) :=
      congrArg Units.val (hs₂ g)
    show (r g).val.map (f₂.comp f₁) * bd Q₁.val Q₂.val =
      bd Q₁.val Q₂.val * (bd (s₁ g).val (s₂ g).val).map (algebraMap _ (FractionRing (PowerSeries K')))
    rw [hrr, bd_map, bd_map, bd_mul, bd_mul, e₁, e₂]
end

