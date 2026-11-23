module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LcOfKer
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem lc_of_ker {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N]
    (τ : Representation ℤ D N) (h : IsOpen (τ.ker : Set D)) : IsLocallyConstant fun s => τ s := by
  rw [IsLocallyConstant.iff_exists_open]
  intro s
  refine ⟨(fun y => s⁻¹ * y) ⁻¹' (τ.ker : Set D), h.preimage (continuous_const_mul s⁻¹), ?_, ?_⟩
  · show s⁻¹ * s ∈ τ.ker
    rw [inv_mul_cancel]
    exact one_mem _
  · intro y hy
    have hy' : τ (s⁻¹ * y) = 1 := hy
    calc τ y = τ (s * (s⁻¹ * y)) := by rw [mul_inv_cancel_left]
      _ = τ s * τ (s⁻¹ * y) := map_mul τ _ _
      _ = τ s := by rw [hy', mul_one]

private theorem cnt {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N] [Finite N]
    (σ τ : Representation ℤ D N) (e : N ≃+ N) (he : ∀ s x, σ s (e x) = e (τ s x)) (h : IsOpen (τ.ker : Set D))
    (A : AddSubgroup (D → N)) [Finite A] (hA : (A : Set (D → N)) ⊆ Zc τ) (T : Set N)
    (hT : ∀ Y, (fun s => τ s Y - Y) ∈ A → Y ∈ T) :
    ∃ Z : AddSubgroup (D → N), (Z : Set (D → N)) = {z | ∃ z' ∈ A, ∃ Y, ∀ s, z s = e (z' s) + (σ s Y - Y)} ∧
      (Z : Set (D → N)) ⊆ Zc σ ∧ (∀ Y, (fun s => σ s Y - Y) ∈ Z) ∧
      Nat.card A * Nat.card N ≤ Nat.card Z * Nat.card T := by
  classical
  let ψ : ↥A × N →+ (D → N) :=
    { toFun := fun p => fun s => e ((p.1 : D → N) s) + (σ s p.2 - p.2)
      map_zero' := by
        funext s
        simp
      map_add' := by
        intro p q
        funext s
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, Pi.add_apply, map_add (f := _)]
        abel }
  have hψ : ∀ p : ↥A × N, ∀ s, ψ p s = e ((p.1 : D → N) s) + (σ s p.2 - p.2) := fun p s => rfl
  have hlc : ∀ Y : N, IsLocallyConstant fun s => σ s Y := by
    intro Y
    have h1 : (fun s => σ s Y) = fun s => e (τ s (e.symm Y)) := by
      funext s
      rw [← he, AddEquiv.apply_symm_apply]
    rw [h1]
    exact (lc_of_ker τ h).comp fun f => e (f (e.symm Y))
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨a, Y⟩, rfl⟩
      exact ⟨a, a.2, Y, fun s => rfl⟩
    · rintro ⟨z', hz', Y, hz⟩
      exact ⟨(⟨z', hz'⟩, Y), funext fun s => (hz s).symm⟩
  · rintro z ⟨⟨a, Y⟩, rfl⟩
    have ha := hA a.2
    refine ⟨?_, ?_⟩
    · have h2 : IsLocallyConstant fun s => e ((a : D → N) s) := ha.1.comp e
      exact h2.add ((hlc Y).sub (IsLocallyConstant.const Y))
    · intro s t
      simp only [hψ]
      rw [ha.2 s t]
      simp only [map_add (f := _), map_sub, he, map_mul, Module.End.mul_apply]
      abel
  · intro Y
    exact ⟨(0, Y), funext fun s => by simp [hψ]⟩
  · have hcard : Nat.card (↥A × N) = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
    have key : ∀ p : ψ.ker, (fun s => τ s (-e.symm p.1.2) - -e.symm p.1.2) = (p.1.1 : D → N) := by
      rintro ⟨⟨a, Y⟩, hp⟩
      have hp' : ∀ s, e ((a : D → N) s) + (σ s Y - Y) = 0 := fun s => congrFun hp s
      show (fun s => τ s (-e.symm Y) - -e.symm Y) = (a : D → N)
      funext s
      apply e.injective
      simp only [map_sub, map_neg, AddEquiv.apply_symm_apply, ← he]
      rw [eq_neg_of_add_eq_zero_left (hp' s)]
      abel
    let f : ψ.ker → T := fun p => ⟨-e.symm p.1.2, hT _ (by rw [key p]; exact p.1.1.2)⟩
    have hf : Function.Injective f := by
      intro p q hpq
      have h2 : p.1.2 = q.1.2 := by
        have h3 : -e.symm p.1.2 = -e.symm q.1.2 := congrArg Subtype.val hpq
        exact e.symm.injective (neg_injective h3)
      have h1 : (p.1.1 : D → N) = q.1.1 := by
        rw [← key p, ← key q, h2]
      exact Subtype.ext (Prod.ext (Subtype.ext h1) h2)
    have hker : Nat.card ψ.ker ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    calc Nat.card A * Nat.card N = Nat.card (↥A × N) := (Nat.card_prod _ _).symm
      _ = Nat.card ψ.range * Nat.card ψ.ker := hcard
      _ ≤ Nat.card ψ.range * Nat.card T := Nat.mul_le_mul_left _ hker

private theorem card_upT (R : Type) [Zero R] [Finite R] :
    Nat.card {Y : Matrix (Fin 3) (Fin 3) R | UpT Y} ≤ Nat.card R ^ 6 := by
  classical
  have hP : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hinj : Function.Injective
      (fun Y : {Y : Matrix (Fin 3) (Fin 3) R | UpT Y} =>
        fun p : {p : Fin 3 × Fin 3 // p.1 ≤ p.2} => (Y : Matrix (Fin 3) (Fin 3) R) p.1.1 p.1.2) := by
    rintro ⟨Y, hY⟩ ⟨Y', hY'⟩ e
    apply Subtype.ext
    ext i j
    show Y i j = Y' i j
    by_cases hij : i ≤ j
    · exact congrFun e ⟨(i, j), hij⟩
    · have hji : j < i := lt_of_not_ge hij
      have h1 : UpT Y := hY
      have h2 : UpT Y' := hY'
      rw [h1 i j hji, h2 i j hji]
  calc Nat.card {Y : Matrix (Fin 3) (Fin 3) R | UpT Y}
      ≤ Nat.card ({p : Fin 3 × Fin 3 // p.1 ≤ p.2} → R) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card R ^ 6 := by rw [Nat.card_fun, hP]

private def cjE {R : Type} [CommRing R] (g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R ≃+ Matrix (Fin 3) (Fin 3) R where
  toFun X := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * (g : Matrix (Fin 3) (Fin 3) R)
  invFun X := (g : Matrix (Fin 3) (Fin 3) R) * X * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
  left_inv X := by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]
  right_inv X := by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]

private theorem ad_cj {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {F : Frame l (ResidueField O)} (B : Box F 3 O) (k : ℕ) (v : F.V) (s : F.Gv v)
    (X : Matrix (Fin 3) (Fin 3) (Ok l O k)) :
    adK B k (F.loc v s) (cjE ((boxK B k).g v) X) = cjE ((boxK B k).g v) (cj k (triOf B v) s X) := by
  have hr : (B.r (F.loc v s)).right = 1 := by
    rw [B.nu]
    exact (F.loc0 v s).2
  have e1 : ∀ A : GL (Fin 3) O, (↑A : Matrix (Fin 3) (Fin 3) O).map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k})) =
      ↑(GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k})) A) := fun A => rfl
  simp only [adK, Box.ad, adRep, GG.ad, boxK, Box.map, GG.map, cjE, cj, triOf, MonoidHom.comp_apply,
    MonoidHom.coe_mk, OneHom.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk, e1]
  show GG.adFun (m := 3) (R := Ok l O k) _ _ = _
  simp only [GG.adFun, GG.mat, SemidirectProduct.map_left, SemidirectProduct.map_right, MonoidHom.id_apply, hr,
    if_true, map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc,
    Units.inv_mul_cancel_left, Units.mul_inv_cancel_left, Units.inv_mul, Units.mul_inv, Matrix.mul_one]

theorem UpperTheory.V.Z.J.zvCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ k, 0 < k → ∀ v, (ZF (l := l) (F.Iv v) k (triOf B v)).Finite → ∃ Z : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)), (Z : Set _) = Zv B k v ∧ (Z : Set _) ⊆ Zc ((adK B k).comp (F.loc v)) ∧ (∀ Y, (fun s => adK B k (F.loc v s) Y - Y) ∈ Z) ∧ (ZF (l := l) (F.Iv v) k (triOf B v)).ncard * Nat.card (Ok l O k) ^ 9 ≤ Nat.card Z * Nat.card (Ok l O k) ^ 6 := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B hlift hOf hCont k hk v hfin
  classical
  obtain ⟨hfinOk, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfinOk k
  have htri := (triOk l O F C₀ hF hl ρ B hlift hOf hCont v).1
  obtain ⟨⟨ρc, hρc, hker⟩, -, -, -, hup⟩ := cjFacts l O (F.Gv v) (triOf B v) k hl htri
  let A : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
    { carrier := ZF (l := l) (F.Iv v) k (triOf B v)
      add_mem' := by
        rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
        refine ⟨ha1.add hb1, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.add_apply]
          rw [ha2, hb2, ← hρc, ← hρc, ← hρc, map_add (f := _)]
          abel
        · intro s i j hij
          simp only [Pi.add_apply, Matrix.add_apply, ha3 s i j hij, hb3 s i j hij, add_zero]
        · intro s hs i
          simp only [Pi.add_apply, Matrix.add_apply, ha4 s hs i, hb4 s hs i, add_zero]
      zero_mem' := by
        refine ⟨IsLocallyConstant.const 0, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.zero_apply]
          rw [← hρc, map_zero, add_zero]
        · intro s i j hij
          rfl
        · intro s hs i
          rfl
      neg_mem' := by
        rintro a ⟨ha1, ha2, ha3, ha4⟩
        refine ⟨ha1.neg, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.neg_apply]
          rw [ha2, ← hρc, ← hρc, map_neg, neg_add]
        · intro s i j hij
          simp only [Pi.neg_apply, Matrix.neg_apply, ha3 s i j hij, neg_zero]
        · intro s hs i
          simp only [Pi.neg_apply, Matrix.neg_apply, ha4 s hs i, neg_zero] }
  have hA : (A : Set (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k))) ⊆ Zc ρc := by
    rintro z ⟨h1, h2, -, -⟩
    exact ⟨h1, fun s t => by rw [h2, hρc]⟩
  haveI : Finite A := hfin.to_subtype
  have hT : ∀ Y, (fun s => ρc s Y - Y) ∈ A → Y ∈ {Y : Matrix (Fin 3) (Fin 3) (Ok l O k) | UpT Y} := by
    rintro Y ⟨-, -, h3, -⟩
    exact hup Y fun s => by
      have := h3 s
      simpa only [hρc] using this
  have he : ∀ s x, ((adK B k).comp (F.loc v)) s (cjE ((boxK B k).g v) x) =
      cjE ((boxK B k).g v) (ρc s x) := by
    intro s x
    rw [hρc]
    exact ad_cj B k v s x
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := cnt _ ρc (cjE ((boxK B k).g v)) he hker A hA _ hT
  refine ⟨Z, ?_, hZ2, hZ3, ?_⟩
  · rw [hZ1]
    rfl
  · have hN : Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) = Nat.card (Ok l O k) ^ 9 := by
      show Nat.card (Fin 3 → Fin 3 → Ok l O k) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul]
    have hAc : Nat.card A = (ZF (l := l) (F.Iv v) k (triOf B v)).ncard :=
      Nat.card_coe_set_eq (ZF (l := l) (F.Iv v) k (triOf B v))
    have hTc := card_upT (Ok l O k)
    calc (ZF (l := l) (F.Iv v) k (triOf B v)).ncard * Nat.card (Ok l O k) ^ 9
        = Nat.card A * Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) := by rw [hAc, hN]
      _ ≤ Nat.card Z * Nat.card {Y : Matrix (Fin 3) (Fin 3) (Ok l O k) | UpT Y} := hZ4
      _ ≤ Nat.card Z * Nat.card (Ok l O k) ^ 6 := Nat.mul_le_mul_left _ hTc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocLow
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private def triG (A : Type) [CommRing A] : AddSubgroup (Matrix (Fin 3) (Fin 3) A) where
  carrier := {X | UpT X}
  add_mem' := fun {a b} ha hb i j h => by
    rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]
  zero_mem' := fun _ _ _ => rfl
  neg_mem' := fun {a} ha i j h => by rw [Matrix.neg_apply, ha i j h, neg_zero]

private theorem triG_card (A : Type) [CommRing A] [Finite A] : Nat.card A ^ 6 ≤ Nat.card (triG A) := by
  classical
  let f : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2} → A) → triG A := fun g =>
    ⟨fun i j => if h : i ≤ j then g ⟨(i, j), h⟩ else 0, by
      show UpT _
      intro i j hij
      simp [not_le.mpr hij]⟩
  have hf : Function.Injective f := by
    intro g g' hgg
    funext p
    have := congrArg (fun x : triG A => (x : Matrix (Fin 3) (Fin 3) A) p.1.1 p.1.2) hgg
    simpa [f, p.2] using this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun] at h1
  have h6 : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2} = 6 := by
    rw [Nat.card_eq_fintype_card]; decide
  rwa [h6] at h1

private def zcG {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    AddSubgroup (D → N) where
  carrier := Zc ρ
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
    simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add (f := _)]; abel⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
    simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩

private theorem local_lower_triangular_cohomology (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [Finite A] (D : Type) [Group D]
    [TopologicalSpace D] [IsTopologicalGroup D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d k : ℕ) (hk : 0 < k)
    (hA : ∀ x : A, l ^ k • x = 0) (hLE : LE l D ε d) (hI : GenI l I d)
    (c : D → Matrix (Fin 3) (Fin 3) A → Matrix (Fin 3) (Fin 3) A)
    (ρ : Representation ℤ D (Matrix (Fin 3) (Fin 3) A)) (hc : ∀ s X, ρ s X = c s X) (ho : IsOpen (ρ.ker : Set D))
    (hT : ∀ s X, UpT X → UpT (c s X) ∧ ∀ i, c s X i i = X i i)
    (W : Set (D → Matrix (Fin 3) (Fin 3) A))
    (hW : ∀ z, z ∈ W ↔ IsLocallyConstant z ∧ (∀ s s', z (s * s') = z s + c s (z s')) ∧ (∀ s, UpT (z s)) ∧
      ∀ s ∈ I, ∀ i, z s i i = 0) :
    W.Finite ∧ Nat.card A ^ (6 + 3 * d) ≤ W.ncard := by
  classical
  have hAm : ∀ x : Matrix (Fin 3) (Fin 3) A, l ^ k • x = 0 := fun x => by
    ext i j; simp [hA]
  have hWZ : W ⊆ Zc ρ := fun z hz => by
    obtain ⟨h1, h2, -, -⟩ := (hW z).1 hz
    exact ⟨h1, fun s t => by rw [h2, hc]⟩
  have hWfin : W.Finite := ((hLE k hk _ ρ hAm ho).1).subset hWZ
  refine ⟨hWfin, ?_⟩
  have hmem : ∀ s (x : triG A), ρ s x.1 ∈ triG A := fun s x => by
    show UpT _
    rw [hc]; exact (hT s x.1 x.2).1
  let f : D → (triG A →+ triG A) := fun s =>
    { toFun := fun x => ⟨ρ s x.1, hmem s x⟩
      map_zero' := Subtype.ext (map_zero (ρ s))
      map_add' := fun x y => Subtype.ext (map_add (ρ s) x.1 y.1) }
  let ρ' : Representation ℤ D (triG A) :=
    { toFun := fun s => (f s).toIntLinearMap
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show ρ 1 x.1 = x.1
        rw [map_one]; rfl)
      map_mul' := fun s t => LinearMap.ext fun x => Subtype.ext (by
        show ρ (s * t) x.1 = ρ s (ρ t x.1)
        rw [map_mul]; rfl) }
  have hρ' : ∀ s (x : triG A), (ρ' s x).1 = ρ s x.1 := fun s x => rfl
  have hker' : IsOpen (ρ'.ker : Set D) := by
    refine Subgroup.isOpen_mono (fun s hs => ?_) ho
    rw [MonoidHom.mem_ker] at hs ⊢
    exact LinearMap.ext fun x => Subtype.ext (by rw [hρ', hs]; rfl)
  have hNk : ∀ x : triG A, l ^ k • x = 0 := fun x =>
    Subtype.ext (by rw [AddSubgroup.coe_nsmul, hAm]; rfl)
  obtain ⟨hZfin, hZcard⟩ := hLE k hk (triG A) ρ' hNk hker'
  have h0 : (0 : D → triG A) ∈ Zc ρ' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  have hpos : 0 < (Zc ρ').ncard := (Set.ncard_pos hZfin).mpr ⟨0, h0⟩
  have hHom : 0 < (HomMu l k ε ρ').ncard := by
    rcases Nat.eq_zero_or_pos (HomMu l k ε ρ').ncard with h | h
    · rw [hZcard, h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  have hbig : Nat.card A ^ (6 + 6 * d) ≤ (Zc ρ').ncard := by
    rw [hZcard]
    calc Nat.card A ^ (6 + 6 * d) = (Nat.card A ^ 6) ^ (1 + d) := by
          rw [← pow_mul]; congr 1; ring
      _ ≤ Nat.card (triG A) ^ (1 + d) := Nat.pow_le_pow_left (triG_card A) _
      _ ≤ _ := Nat.le_mul_of_pos_right _ hHom
  let Z := zcG ρ'
  haveI : Finite Z := hZfin.to_subtype
  let p : Fin 3 → (triG A →+ A) := fun j =>
    { toFun := fun x => x.1 j j, map_zero' := rfl, map_add' := fun x y => rfl }
  have hp : ∀ z ∈ Z, IsLocallyConstant z ∧
      ∀ (j : Fin 3) (s s' : D), p j (z (s * s')) = p j (z s) + p j (z s') := by
    intro z hz
    have hz' : z ∈ Zc ρ' := hz
    refine ⟨hz'.1, fun j s s' => ?_⟩
    show (z (s * s')).1 j j = (z s).1 j j + (z s').1 j j
    rw [hz'.2 s s']
    show (z s).1 j j + (ρ s (z s').1) j j = _
    rw [hc, (hT s _ (z s').2).2 j]
  have hcut := wtCut l D I d k 3 A (triG A) hI hA Z inferInstance p hp
  have hZc : Nat.card Z = (Zc ρ').ncard := Nat.card_coe_set_eq (Zc ρ')
  have hSW : {z | z ∈ Z ∧ ∀ (j : Fin 3), ∀ s ∈ I, p j (z s) = 0}.ncard ≤ W.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun z s => (z s).1) ?_ ?_ hWfin
    · rintro z ⟨hz, hI0⟩
      have hz' : z ∈ Zc ρ' := hz
      rw [hW]
      refine ⟨hz'.1.comp _, fun s s' => ?_, fun s => (z s).2, fun s hs i => hI0 i s hs⟩
      show (z (s * s')).1 = (z s).1 + c s (z s').1
      rw [hz'.2 s s', ← hc]; rfl
    · intro z _ z' _ h
      funext s; exact Subtype.ext (congrFun h s)
  have hApos : 0 < Nat.card A ^ (3 * d) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hApos
  calc Nat.card A ^ (6 + 3 * d) * Nat.card A ^ (3 * d) = Nat.card A ^ (6 + 6 * d) := by
        rw [← pow_add]; congr 1; ring
    _ ≤ (Zc ρ').ncard := hbig
    _ = Nat.card Z := hZc.symm
    _ ≤ _ := hcut
    _ ≤ W.ncard * Nat.card A ^ (3 * d) := Nat.mul_le_mul_right _ hSW

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.locLow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ k, 0 < k → (ZF (l := l) I k t).Finite ∧ Nat.card (Ok l O k) ^ (6 + 3 * d) ≤ (ZF (l := l) I k t).ncard := by
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hI ht k hk
  obtain ⟨hf, -, hA, -⟩ := okFin l O hl
  obtain ⟨⟨ρ, hc, ho⟩, -, hT, -⟩ := cjFacts l O D t k hl ht
  haveI := hf k
  exact local_lower_triangular_cohomology l (Ok l O k) D I ε d k hk (hA k) hLE hI (cj k t) ρ hc ho
    (fun s X hX => ⟨(hT s X hX).1, (hT s X hX).2.1⟩) _ (fun _ => Iff.rfl)
end

