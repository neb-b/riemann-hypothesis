module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.FlDefs

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.AwayPartMulIotaWPart
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Fl

section Blocks

variable {R S : Type} [CommRing R] [CommRing S] {c N : ℕ} {n : Fin c → ℕ}

theorem one_apply_blk (e : (Σ a, Fin (n a)) ≃ Fin N) (a : Fin c) (i j : Fin (n a)) :
    (1 : Matrix (Fin N) (Fin N) R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (Fin (n a)) (Fin (n a)) R) i j := by
  simp [Matrix.one_apply]

theorem one_apply_blk_ne (e : (Σ a, Fin (n a)) ≃ Fin N) {a b : Fin c} (h : a ≠ b) (i : Fin (n a)) (j : Fin (n b)) :
    (1 : Matrix (Fin N) (Fin N) R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  rw [Matrix.one_apply_ne]
  intro h'
  exact h (congrArg Sigma.fst (e.injective h'))

theorem cornerGL_apply {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g : Matrix (Fin a) (Fin a) S) i j =
      (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g : Matrix (Fin a) (Fin a) R) i j) :=
  rfl

theorem cornerGL_leviEmb (e : (Σ a, Fin (n a)) ≃ Fin N) (s : R →ₙ+* S) (m : ∀ a, GL (Fin (n a)) R) :
    cornerGL N s (leviEmb R e m) = leviEmb S e fun a => cornerGL (n a) s (m a) := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  rw [cornerGL_apply]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same, cornerGL_apply, one_apply_blk, one_apply_blk]
  · rw [leviEmb_apply_ne R e m hab, leviEmb_apply_ne S e _ hab, one_apply_blk_ne e hab,
      one_apply_blk_ne e hab, map_zero]
    simp

theorem cornerGL_mem_unipRad (e : (Σ a, Fin (n a)) ≃ Fin N) (s : R →ₙ+* S) {u : GL (Fin N) R}
    (hu : u ∈ unipRad R e) : cornerGL N s u ∈ unipRad S e := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hu
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := fun h' => by subst h'; exact lt_irrefl _ hij
    rw [cornerGL_apply, h1 hij, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne, map_zero]
    simp
  · rw [cornerGL_apply, h2 a i j, one_apply_blk, one_apply_blk]
    simp

end Blocks

variable {E : Type} [Field E] [NumberField E]

theorem glAf_ext {N : ℕ} {x y : GL (Fin N) (Af E)}
    (H : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) :
    x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_
  have := congrArg (fun z : GL (Fin N) (v.adicCompletion E) => z.val i j) (H v)
  simp only [GeneralLinearGroup.map_apply] at this
  exact this

theorem locGL_commute {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) (x : GL (Fin N) (Af E)) (g : GL (Fin N) (w.adicCompletion E))
    (hx : GeneralLinearGroup.map (pLoc E w) x = 1) : locGL E N w g * x = x * locGL E N w g := by
  refine glAf_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [hx, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

variable {N : ℕ} {w : HeightOneSpectrum (𝓞 E)}

theorem wPart_apply (g : GA E N) :
    wPart N w g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  ext i j
  rfl

theorem wPart_iota (x : GL (Fin N) (w.adicCompletion E)) : wPart N w (iota N w x) = x := by
  rw [wPart_apply, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL]

theorem wPart_awayPart (g : GA E N) : wPart N w (awayPart N w g) = 1 := by
  rw [awayPart, map_mul, map_inv, wPart_iota, mul_inv_cancel]

theorem awayPart_mul_iota_wPart (g : GA E N) : awayPart N w g * iota N w (wPart N w g) = g := by
  rw [awayPart, inv_mul_cancel_right]

theorem commute_iota [_root_.NumberField.IsTotallyComplex E] {y : GA E N} (hy : wPart N w y = 1) (x : GL (Fin N) (w.adicCompletion E)) :
    y * iota N w x = iota N w x * y := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, MonoidHom.comp_apply, pInf_finGL, mul_one, one_mul]
  · simp only [map_mul, MonoidHom.comp_apply, pFin_finGL]
    refine (locGL_commute w _ x ?_).symm
    rw [← wPart_apply]
    exact hy

variable {c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N)

theorem iota_leviEmb (x : ∀ i, GL (Fin (n i)) (w.adicCompletion E)) :
    iota N w (leviEmb (w.adicCompletion E) (stdBlocks n h) x) =
      leviEmb (Ad E) (stdBlocks n h) fun i => iota (n i) w (x i) := by
  change cornerGL N (sFin E) (cornerGL N (sLoc E w) _) = _
  rw [cornerGL_leviEmb, cornerGL_leviEmb]
  rfl

theorem iota_mem_unipRad {u : GL (Fin N) (w.adicCompletion E)} (hu : u ∈ unipRad (w.adicCompletion E) (stdBlocks n h)) :
    iota N w u ∈ unipRad (Ad E) (stdBlocks n h) := by
  change cornerGL N (sFin E) (cornerGL N (sLoc E w) u) ∈ _
  exact cornerGL_mem_unipRad _ _ (cornerGL_mem_unipRad _ _ hu)

end PositivityTheory.Rg.Rs.C3.Fl

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.ExistsUpperUnitaryComplex
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.SmGL
open scoped ComplexOrder

namespace PositivityTheory.Rg.Rs.C3.Fl

theorem exists_upper_unitary_complex {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g) :
    ∃ T : Matrix (Fin N) (Fin N) ℂ, IsUnit T ∧ (∀ i j : Fin N, j < i → T i j = 0) ∧
      T * g ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  let g' : Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ := g
  have hg' : IsUnit g' := hg
  have hinj : Function.Injective fun v => v ᵥ* g' := by
    obtain ⟨u, hu⟩ := hg'
    intro v w hvw
    have := congrArg (fun x => x ᵥ* (u⁻¹ : (Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ)ˣ).1) hvw
    simpa [← hu, vecMul_vecMul] using this
  have hS : (g' * g'ᴴ).PosDef := PosDef.mul_conjTranspose_self g' hinj
  set L := LDL.lowerInv hS with hL
  have hD : LDL.diag hS = L * (g' * g'ᴴ) * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hLinj : Function.Injective fun v => v ᵥ* L := by
    intro v w hvw
    have := congrArg (fun x => x ᵥ* ⅟L) hvw
    simpa [vecMul_vecMul] using this
  have hDpos : (L * (g' * g'ᴴ) * Lᴴ).PosDef := hS.mul_mul_conjTranspose_same hLinj
  set d := LDL.diagEntries hS
  have hd : ∀ i, 0 < (d i).re ∧ (d i).im = 0 := by
    intro i
    have := hDpos.diag_pos (i := i)
    rw [← hD] at this
    simp only [LDL.diag, diagonal_apply_eq] at this
    exact ⟨(Complex.pos_iff.1 this).1, (Complex.pos_iff.1 this).2.symm⟩
  let s : (Fin N)ᵒᵈ → ℂ := fun i => (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ)
  let T' : Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ := diagonal s * L
  have hT : T' * (g' * g'ᴴ) * T'ᴴ = 1 := by
    have e1 : T' * (g' * g'ᴴ) * T'ᴴ = diagonal s * LDL.diag hS * diagonal (star s) := by
      rw [hD]; simp only [T', conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc]
    rw [e1, LDL.diag, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hdi : d i = ((d i).re : ℂ) := Complex.ext rfl (by simp [(hd i).2])
    have hr := (hd i).1
    change (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ) * d i * star (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ) = 1
    rw [Complex.star_def, Complex.conj_ofReal]
    generalize (d i).re = r at hdi hr ⊢
    rw [hdi]
    have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    have hne : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
    rw [Real.sq_sqrt hr.le]
  refine ⟨T', ?_, ?_, ?_⟩
  · have h1 : T' * (g' * (T' * g')ᴴ) = 1 := by
      rw [conjTranspose_mul, ← hT]; simp only [Matrix.mul_assoc]
    exact ⟨⟨T', _, h1, mul_eq_one_comm.1 h1⟩, rfl⟩
  · intro i j hij
    have h0 : L (OrderDual.toDual i) (OrderDual.toDual j) = 0 := LDL.isLowerTriangular_lowerInv hS hij
    change (diagonal s * L) (OrderDual.toDual i) (OrderDual.toDual j) = 0
    rw [diagonal_mul]
    exact mul_eq_zero_of_right _ h0
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
    have : T' * g' * (T' * g')ᴴ = 1 := by
      rw [conjTranspose_mul, ← hT]; simp only [Matrix.mul_assoc]
    exact this

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem exists_borel_unitary {N : ℕ} (y : GL (Fin N) (Cinf E)) :
    ∃ (b : GL (Fin N) (Cinf E)) (k : Kinf E N),
      (∀ i j : Fin N, j < i → (b : Matrix (Fin N) (Fin N) (Cinf E)) i j = 0) ∧ y = b * Unitary.toUnits k := by
  classical
  let ev : InfinitePlace E → Cinf E →+* ℂ := fun τ => Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) τ
  have hu : ∀ τ, IsUnit ((y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev τ)) := fun τ =>
    (GeneralLinearGroup.map (ev τ) y).isUnit
  choose T _ hTup hTun using fun τ => exists_upper_unitary_complex _ (hu τ)
  let T' : Matrix (Fin N) (Fin N) (Cinf E) := fun i j τ => T τ i j
  have hev : ∀ τ, T'.map (ev τ) = T τ := fun τ => rfl
  have key : T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E))) = 1 := by
    have hmap : ∀ τ, (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) *
        star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))).map (ev τ) = 1 := by
      intro τ
      have e1 : (T' * (y : Matrix (Fin N) (Fin N) (Cinf E))).map (ev τ) = T τ * (y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev τ) := by
        rw [Matrix.map_mul, hev]
      have e2 : (star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))).map (ev τ) =
          star ((T' * (y : Matrix (Fin N) (Fin N) (Cinf E))).map (ev τ)) := by
        ext i j; rfl
      rw [Matrix.map_mul, e2, e1]
      exact mem_unitaryGroup_iff.1 (hTun τ)
    ext i j τ
    have := congrFun (congrFun (hmap τ) i) j
    rw [Matrix.map_apply] at this
    change ((T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))) i j) τ = _
    refine this.trans ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h1 : T' * ((y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))) = 1 := by
    rw [← Matrix.mul_assoc, key]
  let U : (Matrix (Fin N) (Fin N) (Cinf E))ˣ := ⟨T', _, h1, mul_eq_one_comm.1 h1⟩
  have hk : T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) ∈ Matrix.unitaryGroup (Fin N) (Cinf E) :=
    mem_unitaryGroup_iff.2 key
  refine ⟨U⁻¹, ⟨_, hk⟩, ?_, ?_⟩
  · have hT : T'.BlockTriangular id := fun i j hij => funext fun τ => hTup τ i j hij
    have : Invertible T' := U.invertible
    have hinv := blockTriangular_inv_of_blockTriangular hT
    intro i j hij
    rw [Matrix.coe_units_inv]
    exact hinv hij
  · refine Units.ext ?_
    change (y : Matrix (Fin N) (Fin N) (Cinf E)) =
      ((U⁻¹ : (Matrix (Fin N) (Fin N) (Cinf E))ˣ) : Matrix (Fin N) (Fin N) (Cinf E)) * (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))
    rw [← Matrix.mul_assoc]
    change _ = ((U⁻¹ * U : (Matrix (Fin N) (Fin N) (Cinf E))ˣ) : Matrix (Fin N) (Fin N) (Cinf E)) * (y : Matrix (Fin N) (Fin N) (Cinf E))
    rw [inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem sum_castLE_eq {c : ℕ} (d : Fin c → ℕ) {m : ℕ} (hm : m ≤ c) :
    ∑ x : Fin m, d (Fin.castLE hm x) = ∑ k ∈ Finset.range m, (if h : k < c then d ⟨k, h⟩ else 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < c then d ⟨k, h⟩ else 0) m]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dite_eq_left (lt_of_lt_of_le x.2 hm)]
  rfl

theorem blk_lt_stdBlocks {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) {i j : Fin N}
    (hij : blk (stdBlocks n h) j < blk (stdBlocks n h) i) : j < i := by
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks n h).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks n h).surjective j
  simp only [blk_apply] at hij
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, sum_castLE_eq, sum_castLE_eq]
  have h1 : ∑ k ∈ Finset.range (b + 1), (if h : k < c then n ⟨k, h⟩ else 0) ≤
      ∑ k ∈ Finset.range a, (if h : k < c then n ⟨k, h⟩ else 0) :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hij)
  rw [Finset.sum_range_succ, dite_eq_left b.2] at h1
  simp only [Fin.eta] at h1
  have h2 : (j' : ℕ) < n b := j'.2
  omega

theorem mem_parab_of_upper (R : Type) [CommRing R] {c N : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) {g : GL (Fin N) R}
    (hg : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) R) i j = 0) : g ∈ parab R (stdBlocks n h) :=
  mem_parab.2 fun i j hij => hg i j (blk_lt_stdBlocks n h hij)

end PositivityTheory.Rg.Rs.C3.Fl

end
end

