module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetPush
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mapL {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (M.map j * Z).map p = M * Z.map p := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum, hp]

private theorem mapR {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (Z * M.map j).map p = Z.map p * M := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, hp, mul_comm]

private def ddJ {A B : Type} [CommRing A] [CommRing B] (g : ℕ) (j : A →+* B) : DD A g →+* DD B g where
  toFun d := ⟨j d.a, fun i => j (d.ep i), fun i => j (d.ep' i), j d.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private def ddP {A B : Type} [CommRing A] [CommRing B] (g : ℕ) (p : B →+ A) : DD B g →+ DD A g where
  toFun d := ⟨p d.a, fun i => p (d.ep i), fun i => p (d.ep' i), p d.eta⟩
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private theorem map_additive_mem_symmetric_deformation {A B : Type} [CommRing A] [CommRing B] {g n a : ℕ} (p : B →+ A)
    (Z : Matrix (Fin n) (Fin n) (DD B g)) (hZ : Z ∈ pairedDualFirstOrderDualMatrixSpace n B B g a) : Z.map (ddP g p) ∈ pairedDualFirstOrderDualMatrixSpace n A A g a := by
  have key : ∀ (b1 b2 b3 b4 : Bool) (y : DD B g), y ∈ ddPart B B g b1 b2 b3 b4 →
      ddP g p y ∈ ddPart A A g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 y ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · change p y.a = 0
      rw [h1 e, map_zero]
    · funext i
      change p (y.ep i) = 0
      rw [h2 e]; exact map_zero p
    · funext i
      change p (y.ep' i) = 0
      rw [h3 e]; exact map_zero p
    · change p y.eta = 0
      rw [h4 e, map_zero]
  exact fun r s => ⟨fun e => key _ _ _ _ _ ((hZ r s).1 e), fun e => key _ _ _ _ _ ((hZ r s).2 e)⟩

private theorem sum_dd {X ι : Type} [CommRing X] {g : ℕ} (s : Finset ι) (f : ι → DD X g) :
    ∑ i ∈ s, f i = ⟨∑ i ∈ s, (f i).a, fun j => ∑ i ∈ s, (f i).ep j, fun j => ∑ i ∈ s, (f i).ep' j,
      ∑ i ∈ s, (f i).eta⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty => ext <;> simp
  | insert i s hi ih => ext <;> simp [Finset.sum_insert hi, ih]

private theorem exJP {A B : Type} [CommRing A] [CommRing B] {g g' n a m : ℕ} (e : g' = g) (j : A →+* B)
    (b : Fin m → B) (p : Fin m → B →+ A) (hb : ∀ y, y = ∑ i, j (p i y) * b i)
    (hp : ∀ i a y, p i (j a * y) = a * p i y) :
    ∃ (J : DD A g →+* DD B g') (P : Fin m → DD B g' →+ DD A g),
      (∀ c, J (DD.C c) = DD.C (j c)) ∧
      (∀ K : Fin g → Matrix (Fin n) (Fin n) A, (DD.epM K).map J = DD.epM fun i => (K (Fin.cast e i)).map j) ∧
      (∀ i a y, P i (J a * y) = a * P i y) ∧ (∀ y, y = ∑ i, J (P i y) * DD.C (b i)) ∧
      (∀ i y, (P i y).eta = p i y.eta) ∧
      (∀ i Z, Z ∈ pairedDualFirstOrderDualMatrixSpace n B B g' a → Z.map (P i) ∈ pairedDualFirstOrderDualMatrixSpace n A A g a) ∧
      ∀ Z, Z ∈ pairedDualFirstOrderDualMatrixSpace n A A g a → Z.map J ∈ pairedDualFirstOrderDualMatrixSpace n B B g' a := by
  subst e
  refine ⟨ddJ _ j, fun i => ddP _ (p i), fun c => ?_, fun K => ?_, fun i a y => ?_, fun y => ?_, fun _ _ => rfl,
    fun i Z h => map_additive_mem_symmetric_deformation (p i) Z h, fun Z h => map_additive_mem_symmetric_deformation j.toAddMonoidHom Z h⟩
  · ext <;> simp [ddJ]
  · ext <;> simp [ddJ, DD.epM]
  · ext <;> simp [ddJ, ddP, hp]
  · rw [sum_dd]
    ext <;> simp [ddJ, ddP, ← hb]

theorem UpperTheory.V.Pa.Det.detPush :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ (k : Kap x) (k' : Kap x') (e : k'.g = k.g), (∀ i g, k'.κ i g = (k.κ (Fin.cast e i) g).map j) → ∀ S : Set F.G₀, Detects k S → Detects k' S := by
  intro l _ F n x x' j hE k k' e hκ S hD z hz hell
  obtain ⟨⟨hinj, hloc, hfin, hρ, ha, -⟩, -⟩ := hE
  obtain ⟨m, b, p, -, hb, hp, -, -, r, u, -, hu⟩ := UpperTheory.V.Pa.Det.extFree j hinj hloc hfin
  obtain ⟨J, P, JC, Jep, hP, hB, Peta, PW, JW⟩ := exJP (n := n) (a := x.a) e j b p hb hp
  have hl : (l : x'.A) = 0 := by
    haveI := (UpperTheory.V.Pa.Det.zlUniq l).1 (algebraMap ℤ_[l] x'.K)
    have := congrArg (algebraMap x'.K x'.A) (CharP.cast_eq_zero x'.K l)
    rwa [map_natCast, map_zero] at this
  have he : ∀ g, epsD k' x'.A g = J (epsD k x.A g) := by
    intro g
    have := ((UpperTheory.V.Pa.Det.zlUniq l).2 (algebraMap ℤ_[l] x'.A) (j.comp (algebraMap ℤ_[l] x.A)) hl).1
    exact (congrArg DD.C (DFunLike.congr_fun this ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]))).trans (JC _).symm
  have hr : ∀ g, k'.ρ1 x'.A g = (k.ρ1 x.A g).map J := by
    intro g
    have h1 : x'.ρX (DD x'.A k'.g) g = (x.ρX (DD x.A k.g) g).map J := by
      ext1 a c
      simp only [NP.ρX, hρ, Matrix.map_apply]
      exact (JC _).symm
    rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul, ← h1, Matrix.map_add _ (map_add J), Jep, Matrix.map_one _ (map_zero J) (map_one J)]
    simp only [hκ]
    rfl
  have h3 : (u : x'.A) * ((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) = 1 := u.mul_inv
  have hpow : ∀ N, (DD.C x'.t : DD x'.A k'.g) ^ (r * N) =
      J (DD.C x.t ^ N) * DD.C (((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N) := by
    intro N
    rw [map_pow J, JC, ← map_pow, ← map_pow, ← map_mul, hu, ← mul_pow, mul_right_comm, h3, one_mul, pow_mul]
  obtain ⟨z1, z2, z3, z4⟩ := hz
  have hsm : ∀ i (c : DD x.A k.g) (Z : Matrix (Fin n) (Fin n) (DD x'.A k'.g)), (J c • Z).map (P i) = c • Z.map (P i) := by
    intro i c Z
    ext1 a c
    exact hP _ _ _
  have hzi : ∀ i, (fun g => (z g).map (P i)) ∈ TwZ k x.A := by
    intro i
    refine ⟨fun g => PW i _ (ha ▸ z1 g), fun a c N => ?_, fun g h => ?_, fun g => ?_⟩
    · have := z2 a c (r * N)
      rw [IsLocallyConstant.iff_eventually_eq] at this ⊢
      intro g
      filter_upwards [this g] with h hh
      rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hh ⊢
      obtain ⟨w, hw⟩ := hh
      change _ = (DD.C x'.t : DD x'.A k'.g) ^ (r * N) * w at hw
      refine ⟨P i (DD.C (((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N) * w), ?_⟩
      change P i (z h a c) - P i (z g a c) = (DD.C x.t : DD x.A k.g) ^ N * _
      rw [← map_sub, hw, hpow, mul_assoc, hP]
    · simp only
      rw [z3, Matrix.map_add _ (map_add (P i)), he, hsm, hr, hr, mapR J (P i) (hP i), mapL J (P i) (hP i)]
    · simp only
      rw [z4, Matrix.map_neg _ (map_neg (P i)), he, hsm, Matrix.transpose_map]
  have hli : ∀ i, ∀ σ ∈ S, ell k x.A σ (fun g => (z g).map (P i)) = 0 := by
    intro i σ hσ
    have h0 := hell σ hσ
    simp only [ell] at h0 ⊢
    rw [← mapR J (P i) (hP i), ← hr, ← AddMonoidHom.map_trace, Peta, h0, map_zero]
  choose s Y hY hT hs using fun i => hD _ (hzi i) (hli i)
  have hle : ∀ i, s i ≤ ∑ i, s i := fun i =>
    Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set N := ∑ i, s i with hN
  let d : Fin m → x'.A := fun i => ((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N * b i * j (x.t ^ (N - s i))
  have key : ∀ y : DD x'.A k'.g, ∑ i, d i • J (x.t ^ s i • P i y) = x'.t ^ (r * N) • y := by
    intro y
    conv_rhs => rw [hB y, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change DD.C (d i) * J (DD.C (x.t ^ s i) * P i y) = DD.C (x'.t ^ (r * N)) * _
    have h4 : J ((DD.C x.t : DD x.A k.g) ^ N) = DD.C (j (x.t ^ (N - s i))) * J (DD.C (x.t ^ s i)) := by
      rw [← JC, ← map_mul, ← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow DD.C]
    rw [map_pow DD.C x'.t, hpow, h4]
    simp only [d, map_mul]
    ring
  have hJs : ∀ (c : DD x.A k.g) (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)), (c • Z).map J = J c • Z.map J := by
    intro c Z
    ext1 a c
    exact map_mul J _ _
  refine ⟨r * N, ∑ i, d i • (Y i).map J, ?_, ?_, ?_⟩
  · exact sum_mem fun i _ => Submodule.smul_mem _ _ (ha ▸ JW _ (hY i))
  · rw [Matrix.transpose_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← hT i]
    rw [Matrix.map_neg _ (map_neg J), hJs, ← he, Matrix.transpose_smul, Matrix.transpose_map, smul_neg, smul_comm]
  · funext g
    have h5 : (x'.t ^ (r * N) • z) g = ∑ i, d i • ((x.t ^ s i • fun g => (z g).map (P i)) g).map J := by
      ext1 a c
      rw [Matrix.sum_apply]
      exact (key _).symm
    rw [h5, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]
    simp only
    rw [Matrix.map_sub _ (map_sub J), hJs, Matrix.map_mul, Matrix.map_mul, ← he, ← hr, ← hr, smul_sub,
      Matrix.mul_smul, Matrix.smul_mul, smul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FlagBasis
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem flagBasis_diag_mul {F : Type} [Field F] {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem flagBasis_conj {F : Type} [Field F] {n : ℕ} (b t : GL (Fin n) F)
    (hb : ∀ i j, j < i → b i j = 0) (ht : ∀ i j, j < i → t i j = 0) :
    (∀ i j, j < i → (b⁻¹ * t * b : GL (Fin n) F) i j = 0) ∧
      ∀ i, (b⁻¹ * t * b : GL (Fin n) F) i i = t i i := by
  have hbm : (b : Matrix (Fin n) (Fin n) F).BlockTriangular id := fun i j h => hb i j h
  have htm : (t : Matrix (Fin n) (Fin n) F).BlockTriangular id := fun i j h => ht i j h
  have hbi : ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
    letI := b.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hbm
  have hdiag : ∀ i, ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i *
      (b : Matrix (Fin n) (Fin n) F) i i = 1 := by
    intro i
    rw [← flagBasis_diag_mul hbi hbm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact ((hbi.mul htm).mul hbm) hij
  · rw [Units.val_mul, Units.val_mul, flagBasis_diag_mul (hbi.mul htm) hbm,
      flagBasis_diag_mul hbi htm, mul_right_comm, hdiag, one_mul]

theorem UpperTheory.V.Pa.Det.flagBasis :
    ∀ {K H : Type} [Field K] [Group H] {n a : ℕ} (r : H →* GL (Fin n) (PowerSeries K)) (ψ : Fin n → H →* (PowerSeries K)ˣ), (∀ g, mat r g ∈ Ev (PowerSeries K) (PowerSeries K) n a) → Function.Injective ψ → HasFlag (pushRep (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) r) (fun i => pushCh (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) (ψ i)) → ∃ (w : GL (Fin n) (PowerSeries K)) (ty : Fin n → Bool), (∀ i j : Fin n, decide ((i : ℕ) < a) ≠ ty j → w i j = 0) ∧ ∀ g, (∀ i j, j < i → (w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j = 0) ∧ ∀ i, (w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i i = (ψ i g : PowerSeries K) := by
  intro K H _ _ n a r ψ hev hinj hflag
  set ι := algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) with hι
  have hιi : Function.Injective ι := IsFractionRing.injective _ _
  haveI : Infinite (FractionRing (PowerSeries K)) := by
    refine Infinite.of_injective (fun m : ℕ => ι (PowerSeries.X ^ m)) ?_
    intro m k hmk
    have h := congrArg (fun p => PowerSeries.coeff (R := K) m p) (hιi hmk)
    simp only [PowerSeries.coeff_X_pow, if_true] at h
    by_contra hne
    rw [if_neg hne] at h
    exact one_ne_zero h
  have hev' : ∀ g, mat (pushRep ι r) g ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a := by
    intro g
    have hg := hev g
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
    have h0 := (Submodule.mem_bot _).1 ((hg i j).2 h)
    have e : mat (pushRep ι r) g i j = ι (mat r g i j) := rfl
    rw [e, h0, map_zero]
    exact Submodule.zero_mem _
  have hψ : Function.Injective (fun i => pushCh ι (ψ i)) := by
    intro i j hij
    apply hinj
    ext g
    have := congrArg (fun f : H →* (FractionRing (PowerSeries K))ˣ => ((f g : (FractionRing (PowerSeries K))ˣ) : FractionRing (PowerSeries K))) hij
    rw [hιi this]
  obtain ⟨w0, ty, hw0, htri⟩ := Det.flagF (pushRep ι r) (fun i => pushCh ι (ψ i)) hev' hψ hflag
  obtain ⟨w, b, hb, hwb, hw⟩ :=
    Det.exists_integral_block_iwasawa_decomposition (A := PowerSeries K) (fun i : Fin n => decide ((i : ℕ) < a)) ty w0 hw0
  refine ⟨w, ty, hw, fun g => ?_⟩
  have hmap : GeneralLinearGroup.map ι (w⁻¹ * r g * w) = b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b := by
    rw [map_mul, map_mul, map_inv, hwb, _root_.mul_inv_rev]
    simp only [pushRep, MonoidHom.comp_apply, mul_assoc]
  have hent : ∀ i j, ι ((w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j) =
      (b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b : GL (Fin n) (FractionRing (PowerSeries K))) i j := by
    intro i j
    rw [← hmap]
    rfl
  obtain ⟨hc1, hc2⟩ := flagBasis_conj b (w0⁻¹ * pushRep ι r g * w0) hb (htri g).1
  refine ⟨fun i j hij => hιi ?_, fun i => hιi ?_⟩
  · rw [hent, hc1 i j hij, map_zero]
  · rw [hent, hc2 i, (htri g).2 i]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Infres
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n : ℕ}

private def sgnM (F : Type) [Field F] (n a : ℕ) : Matrix (Fin n) (Fin n) F :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else -1

private theorem sgnM_sq (a : ℕ) : sgnM F n a * sgnM F n a = 1 := by
  rw [sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  split_ifs <;> simp

private theorem sgnM_conj_apply (a : ℕ) (X : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (sgnM F n a * X * sgnM F n a) i j = if ((i : ℕ) < a ↔ (j : ℕ) < a) then X i j else -X i j := by
  simp only [sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj]

private theorem sgnM_ev (a : ℕ) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Ev F F n a) :
    sgnM F n a * X * sgnM F n a = X := by
  have hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) := hX
  ext i j
  rw [sgnM_conj_apply]
  split_ifs with h
  · rfl
  · have h0 : X i j = 0 := by simpa using (hX' i j).2 h
    rw [h0, neg_zero]

private theorem sgnM_od (a : ℕ) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Od F F n a) :
    sgnM F n a * X * sgnM F n a = -X := by
  have hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) := hX
  ext i j
  rw [sgnM_conj_apply, Matrix.neg_apply]
  split_ifs with h
  · have h0 : X i j = 0 := by simpa using (hX' i j).1 h
    rw [h0, neg_zero]
  · rfl

private theorem od_of_sgnM (two : (2 : F) ≠ 0) (a : ℕ) {X : Matrix (Fin n) (Fin n) F}
    (hX : sgnM F n a * X * sgnM F n a = -X) : X ∈ Od F F n a := by
  show ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F))
  intro i j
  refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
  have e := congrFun (congrFun hX i) j
  rw [sgnM_conj_apply, if_pos h, Matrix.neg_apply] at e
  have h2 : (2 : F) * X i j = 0 := by rw [two_mul]; nth_rewrite 1 [e]; ring
  rw [Submodule.mem_bot]
  exact (mul_eq_zero.mp h2).resolve_left two

private theorem sgnM_mul (a : ℕ) (X Y : Matrix (Fin n) (Fin n) F) :
    sgnM F n a * (X * Y) * sgnM F n a = (sgnM F n a * X * sgnM F n a) * (sgnM F n a * Y * sgnM F n a) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (sgnM F n a) (sgnM F n a), sgnM_sq, Matrix.one_mul]

private theorem sgnM_dTw {G : Type} [Group G] (D : DetFr F G n) (χ : G → F) (Y : Matrix (Fin n) (Fin n) F) (g : G) :
    sgnM F n D.a * dTw χ D.r Y g * sgnM F n D.a = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) g := by
  simp only [dTw, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, sgnM_mul,
    sgnM_ev D.a (D.ev g), sgnM_ev D.a (D.ev g⁻¹)]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Det.infres :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), (∀ g h, χ (g * h) = χ g * χ h) → (∀ g ∈ D.G', χ g = 1) → TwCoc χ D.r Set.univ z → (∀ g, z g ∈ Od F F n D.a) → (∀ g ∈ D.G', z g = dTw χ D.r Y g) → ∃ Y' ∈ Od F F n D.a, ∀ g, z g = dTw χ D.r Y' g := by
  intro F G _ _ n D χ z Y hχ hχ' hz hzod hzG
  have two : (2 : F) ≠ 0 := D.two
  have hdTw_sub : ∀ A B g, dTw χ D.r (A - B) g = dTw χ D.r A g - dTw χ D.r B g := by
    intro A B g
    simp only [dTw, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  have hdTw_smul : ∀ (c : F) A g, dTw χ D.r (c • A) g = c • dTw χ D.r A g := by
    intro c A g
    simp only [dTw, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rw [smul_comm]
  have hdTw_neg : ∀ A g, dTw χ D.r (-A) g = -dTw χ D.r A g := by
    intro A g
    simp only [dTw, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
    abel
  have hdc : ∀ A g h, dTw χ D.r A (g * h) = dTw χ D.r A g + χ g • (D.r g * dTw χ D.r A h * D.r g⁻¹) := by
    intro A g h
    simp only [dTw, hχ, _root_.mul_inv_rev, map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc]
    abel
  have hss := sgnM_sq (F := F) (n := n) D.a
  have hcc : ∀ A : Matrix (Fin n) (Fin n) F,
      sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a = A := by
    intro A
    rw [show sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a
        = (sgnM F n D.a * sgnM F n D.a) * A * (sgnM F n D.a * sgnM F n D.a) by
      simp only [Matrix.mul_assoc], hss, Matrix.one_mul, Matrix.mul_one]
  set Y' : Matrix (Fin n) (Fin n) F := (2 : F)⁻¹ • (Y - sgnM F n D.a * Y * sgnM F n D.a) with hY'
  have hY'od : Y' ∈ Od F F n D.a := by
    apply od_of_sgnM two
    rw [hY', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hcc, ← smul_neg, neg_sub]
  have hG' : ∀ h ∈ D.G', z h = dTw χ D.r Y' h := by
    intro h hh
    have h1 := hzG h hh
    have h2 : -z h = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) h := by
      rw [← sgnM_od D.a (hzod h), h1, sgnM_dTw]
    rw [hY', hdTw_smul, hdTw_sub, ← h1, ← h2, sub_neg_eq_add, ← two_smul F (z h), smul_smul,
      inv_mul_cancel₀ two, one_smul]
  have key : ∀ g, z g - dTw χ D.r Y' g = 0 := by
    intro g
    set w : G → Matrix (Fin n) (Fin n) F := fun x => z x - dTw χ D.r Y' x with hw
    have hwc : ∀ x y, w (x * y) = w x + χ x • (D.r x * w y * D.r x⁻¹) := by
      intro x y
      simp only [hw]
      rw [hz x trivial y trivial, hdc]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel
    have hw0 : ∀ h ∈ D.G', w h = 0 := fun h hh => by
      simp only [hw]
      rw [hG' h hh, sub_self]
    have hcomm : ∀ h ∈ D.G', D.r h * w g = w g * D.r h := by
      intro h hh
      have hh' : g⁻¹ * h * g ∈ D.G' := by
        have hm := D.G'.mul_mem (D.comm g⁻¹ h) hh
        simpa [mul_assoc] using hm
      have e1 := hwc g (g⁻¹ * h * g)
      have e2 := hwc h g
      rw [hw0 _ hh', Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero] at e1
      rw [hw0 _ hh, hχ' h hh, one_smul, zero_add] at e2
      have heq : g * (g⁻¹ * h * g) = h * g := by group
      rw [heq, e2] at e1
      calc D.r h * w g = D.r h * w g * (D.r h⁻¹ * D.r h) := by
            rw [← map_mul D.r h⁻¹ h, inv_mul_cancel, map_one, Matrix.mul_one]
        _ = (D.r h * w g * D.r h⁻¹) * D.r h := by simp only [Matrix.mul_assoc]
        _ = w g * D.r h := by rw [e1]
    have hwod : w g ∈ Od F F n D.a := by
      simp only [hw]
      refine Submodule.sub_mem _ (hzod g) ?_
      apply od_of_sgnM two
      rw [sgnM_dTw, sgnM_od D.a hY'od, hdTw_neg]
    exact (Det.central D (w g) hcomm).1 hwod
  exact ⟨Y', hY'od, fun g => sub_eq_zero.mp (key g)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.KapPush
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.kapPush :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ k : Kap x, ∃ (k' : Kap x') (e : k'.g = k.g), (∀ i g, k'.κ i g = (k.κ (Fin.cast e i) g).map j) ∧ ∀ i v, k'.Y i v = (k.Y (Fin.cast e i) v).map j := by
  intro l _ F n x x' j hE k
  obtain ⟨m, b, p, -, hb, hp, -, hc, e, u, -, hu⟩ := UpperTheory.V.Pa.Det.extFree j hE.1.1 hE.1.2.1 hE.1.2.2.1
  obtain ⟨pS, pB, pL⟩ := UpperTheory.V.Pa.Det.pushSel x x' j hE
  have cS := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).1
  have cB := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).2
  obtain ⟨S, hS⟩ := (UpperTheory.V.Pa.Det.selSub F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)).2
  have ha : x'.a = x.a := hE.1.2.2.2.2.1
  refine ⟨⟨k.g, fun i g => (k.κ i g).map j, fun i => pS _ (k.mem i), fun i v => (k.Y i v).map j, ?_,
    fun i v => pL _ _ _ (k.loc i v), ?_, ?_⟩, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i v r s
    refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
    have := (k.Y_mem i v r s).1 (by rw [← ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  · intro c hcB
    have h0 : ∀ i, (fun a => p i (c a)) = 0 := by
      intro i
      apply k.indep
      convert cB i _ hcB using 1
      funext g
      ext r s : 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm (c a), hp, mul_comm]
    funext a
    rw [hb (c a)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show p i (c a) = 0 from congrFun (h0 i) a, map_zero, zero_mul]
  · intro z hz
    choose s c hsc using fun i => k.gen _ (cS i z hz)
    have hle : ∀ i, s i ≤ ∑ i, s i := fun i =>
      Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    set N := ∑ i, s i with hN
    let d : Fin m → x'.A := fun i => ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (x.t ^ (N - s i))
    have h3 : (u : x'.A) ^ N * ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
    have key : ∀ y : x'.A, ∑ i, d i * j (x.t ^ s i * p i y) = x'.t ^ (e * N) * y := by
      intro y
      conv_rhs => rw [hb y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4 : j (x.t ^ (N - s i)) * j (x.t ^ s i) = (u : x'.A) ^ N * x'.t ^ (e * N) := by
        rw [← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow, hu, mul_pow, pow_mul]
      simp only [d, map_mul]
      linear_combination (((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (p i y)) * h4
        + (x'.t ^ (e * N) * b i * j (p i y)) * h3
    refine ⟨e * N, fun a => ∑ i, d i * j (c i a), ?_⟩
    have hm : ∑ i, d i • (fun g => ((x.t ^ s i • (fun g => (z g).map (p i)) - ∑ a, c i a • k.κ a) g).map j) ∈ S := by
      refine S.sum_mem fun i _ => S.smul_mem _ ?_
      have := pB _ (hsc i)
      rw [← hS] at this
      exact this
    rw [← hS, SetLike.mem_coe]
    convert hm using 1
    funext g
    ext r t : 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, map_sum, map_sub, mul_sub, Finset.sum_sub_distrib, key, Finset.sum_mul,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [map_mul, mul_assoc]
end

