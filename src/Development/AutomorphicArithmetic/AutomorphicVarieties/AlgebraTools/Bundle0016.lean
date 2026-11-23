module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsOneBlock
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.units_one_block :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p : ι), (∀ i, o i = p) → ∃ φ : E ≃ₐ[B] Matrix ι ι B, (∀ y i j, φ y i j = T.tr (U.x i * y * T.st (U.x j))) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = T.tr y := by
  intro B E _ _ _ T ι _ _ o U p ho
  obtain ⟨hA, hB, -, hD, hE, hF, -⟩ := units_basic T o U
  have hidem : U.ep p * U.ep p = U.ep p := (U.coi.idem p).eq
  have hte : T.tr (U.ep p) = 1 := U.tr_ep p
  have hxs : ∀ i j, U.x i * T.st (U.x j) = if i = j then U.ep p else 0 := by
    intro i j
    split_ifs with h
    · subst h
      rw [U.x_st, ho]
    · exact hA i j h
  have hex : ∀ j, U.ep p * U.x j = U.x j := by
    intro j
    have h := U.x_mem j
    rw [ho] at h
    calc U.ep p * U.x j = U.ep p * (U.ep p * U.x j * U.ep j) := by rw [h]
      _ = U.ep p * U.ep p * U.x j * U.ep j := by simp only [mul_assoc]
      _ = U.x j := by rw [hidem, h]
  have hE' : ∀ i j y, U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep p := by
    intro i j y
    have h := hE i j y (by rw [ho i, ho j])
    rwa [ho i] at h
  have hpair : ∀ a b : E, a = T.tr a • U.ep p → b = T.tr b • U.ep p → T.tr (a * b) = T.tr a * T.tr b := by
    intro a b ha hb
    calc T.tr (a * b) = T.tr ((T.tr a • U.ep p) * (T.tr b • U.ep p)) := by rw [← ha, ← hb]
      _ = T.tr a * T.tr b := by rw [smul_mul_smul_comm, hidem, map_smul, hte, smul_eq_mul, mul_one]
  let f : E → Matrix ι ι B := fun y => Matrix.of fun i j => T.tr (U.x i * y * T.st (U.x j))
  let g : Matrix ι ι B → E := fun M => ∑ i, ∑ j, M i j • (T.st (U.x i) * U.x j)
  have hfmul : ∀ y z, f (y * z) = f y * f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.mul_apply]
    calc T.tr (U.x i * (y * z) * T.st (U.x j))
        = T.tr (U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j)) := by
          rw [hB, mul_one, mul_assoc (U.x i) y z]
      _ = ∑ k, T.tr ((U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Finset.mul_sum, Finset.sum_mul, map_sum, mul_assoc]
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact hpair _ _ (hE' i k y) (hE' k j z)
  have hfadd : ∀ y z, f (y + z) = f y + f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add (f := _)]
  have hfsmul : ∀ (r : B) y, f (r • y) = r • f y := by
    intro r y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hf1 : f 1 = 1 := by
    ext i j
    simp only [f, Matrix.of_apply, mul_one, hxs, Matrix.one_apply]
    split_ifs <;> simp [hte]
  have hgf : ∀ y, g (f y) = y := by
    intro y
    simp only [g, f, Matrix.of_apply]
    conv_rhs => rw [hF y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := hE' i j y
    set c := T.tr (U.x i * y * T.st (U.x j)) with hc
    rw [h, mul_smul_comm, smul_mul_assoc, mul_assoc, hex]
  have hfg : ∀ M, f (g M) = M := by
    intro M
    ext i j
    have hq : ∀ k l, U.x i * (T.st (U.x k) * U.x l) * T.st (U.x j) = (U.x i * T.st (U.x k)) * (U.x l * T.st (U.x j)) := by
      intro k l
      simp only [mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, g, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, hq, hxs]
    simp [ite_mul, mul_ite, hidem, hte, apply_ite]
  have hfst : ∀ y, f (T.st y) = (f y)ᵀ := by
    intro y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.transpose_apply]
    rw [← T.tr_st (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have hftr : ∀ y, (f y).trace = T.tr y := by
    intro y
    simp only [Matrix.trace, Matrix.diag, f, Matrix.of_apply]
    exact (hD y).symm
  have hcomm : ∀ r : B, f (algebraMap B E r) = algebraMap B (Matrix ι ι B) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hfsmul, hf1]
  let φ : E ≃ₐ[B] Matrix ι ι B := { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg, map_mul' := hfmul, map_add' := hfadd, commutes' := hcomm }
  exact ⟨φ, fun y i j => rfl, hfst, hftr⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.VrRange
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section aux

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι] [DecidableEq ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private noncomputable def vrEnt (w : E) : (U.oddForm p q).Ext :=
  (U.oddForm p q).el (T.tr w)
    (cornerProj B (U.ep p) (U.ep q) w + cornerProj B (U.ep p) (U.ep q) (T.st w))

private noncomputable def vrRec (a b : ι) (z : (U.oddForm p q).Ext) : E :=
  if a = b then z.ev • U.ep a else if a = p then z.od.1 else T.st z.od.1

omit [DecidableEq ι] in
private theorem vrEnt_od (w : E) :
    (vrEnt U p q w).od.1 = U.ep p * w * U.ep q + U.ep p * T.st w * U.ep q := by
  simp only [mul_assoc]; rfl

omit [DecidableEq ι] in
private theorem vrEnt_ev (w : E) : (vrEnt U p q w).ev = T.tr w := rfl

omit [DecidableEq ι] in
private theorem sand (a b c d : ι) (w : E) (hw : U.ep a * w * U.ep b = w) (h : c ≠ a ∨ b ≠ d) :
    U.ep c * w * U.ep d = 0 := by
  rw [← hw]
  simp only [mul_assoc]
  rcases h with h | h
  · rw [← mul_assoc (U.ep c), U.coi.ortho h, zero_mul]
  · rw [U.coi.ortho h, mul_zero, mul_zero, mul_zero]

omit [DecidableEq ι] in
private theorem sand_st (a b : ι) (w : E) (hw : U.ep a * w * U.ep b = w) :
    U.ep b * T.st w * U.ep a = T.st w := by
  conv_rhs => rw [← hw]
  rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]

private theorem ent_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q) (w : E)
    (hw : U.ep a * w * U.ep b = w) :
    ((a = b → (vrEnt U p q w).od = 0) ∧ (a ≠ b → (vrEnt U p q w).ev = 0)) ∧
      vrRec U p q a b (vrEnt U p q w) = w := by
  have hst := sand_st U a b w hw
  refine ⟨⟨fun hab => ?_, fun hab => ?_⟩, ?_⟩
  · rw [← hab] at hw hst
    have h1 : p ≠ a ∨ a ≠ q := by
      rcases ha with h | h
      · exact Or.inr (fun h' => hpq (h.symm.trans h'))
      · exact Or.inl (fun h' => hpq (h'.trans h))
    apply Subtype.ext
    rw [vrEnt_od, sand U a a p q w hw h1, sand U a a p q (T.st w) hst h1, add_zero]
    rfl
  · rw [vrEnt_ev, ← hw]
    exact (units_basic T o U).2.2.1 a b w hab
  · unfold vrRec
    split_ifs with h1 h2
    · rw [← h1] at hw
      rw [vrEnt_ev]
      conv_rhs => rw [← hw, U.corner_eq, hw]
    · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
      rw [h2, hb'] at hw hst
      rw [vrEnt_od, hw, sand U q p p q (T.st w) hst (Or.inl hpq), add_zero]
    · have ha' : a = q := ha.resolve_left h2
      have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
      rw [ha', hb'] at hw hst
      rw [vrEnt_od, sand U q p p q w hw (Or.inl hpq), zero_add, hst, T.st_st]

private theorem rec_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (z : (U.oddForm p q).Ext) (hz : (a = b → z.od = 0) ∧ (a ≠ b → z.ev = 0)) :
    U.ep a * vrRec U p q a b z * U.ep b = vrRec U p q a b z ∧ vrEnt U p q (vrRec U p q a b z) = z := by
  have hid : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hmem : U.ep p * (z.od : E) * U.ep q = z.od := by
    obtain ⟨y, hy⟩ := z.od.2
    rw [← hy]
    show U.ep p * (U.ep p * (y * U.ep q)) * U.ep q = U.ep p * (y * U.ep q)
    rw [← mul_assoc (U.ep p) (U.ep p), hid, mul_assoc, mul_assoc, hid]
  have hoff : U.ep p * T.st (z.od : E) * U.ep q = 0 :=
    sand U q p p q _ (sand_st U p q _ hmem) (Or.inl hpq)
  unfold vrRec
  split_ifs with h1 h2
  · have hod := hz.1 h1
    have hpa : U.ep p * U.ep a * U.ep q = 0 := by
      rcases ha with h | h
      · rw [h, hid, U.coi.ortho hpq]
      · rw [h, U.coi.ortho hpq, zero_mul]
    refine ⟨?_, ?_⟩
    · rw [← h1, mul_smul_comm, smul_mul_assoc, hid, hid]
    · apply Prod.ext
      · change (vrEnt U p q (z.ev • U.ep a)).ev = z.ev
        rw [vrEnt_ev, map_smul, U.tr_ep, smul_eq_mul, mul_one]
      · change (vrEnt U p q (z.ev • U.ep a)).od = z.od
        apply Subtype.ext
        rw [vrEnt_od, hod, map_smul, U.st_ep]
        simp only [mul_smul_comm, smul_mul_assoc, hpa, smul_zero, add_zero]
        rfl
  · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
    have hev := hz.2 h1
    rw [h2, hb']
    refine ⟨hmem, ?_⟩
    apply Prod.ext
    · change (vrEnt U p q (z.od : E)).ev = z.ev
      rw [vrEnt_ev, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · change (vrEnt U p q (z.od : E)).od = z.od
      apply Subtype.ext
      rw [vrEnt_od, hmem, hoff, add_zero]
  · have ha' : a = q := ha.resolve_left h2
    have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
    have hev := hz.2 h1
    rw [ha', hb']
    refine ⟨sand_st U p q _ hmem, ?_⟩
    apply Prod.ext
    · change (vrEnt U p q (T.st (z.od : E))).ev = z.ev
      rw [vrEnt_ev, T.tr_st, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · change (vrEnt U p q (T.st (z.od : E))).od = z.od
      apply Subtype.ext
      rw [vrEnt_od, T.st_st, hmem, hoff, zero_add]

end aux

theorem UpperTheory.V.AlgebraTools.vr_range :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → Function.Injective (U.vr p q) ∧ ∀ Y : Matrix ι ι (U.oddForm p q).Ext, Y ∈ Set.range (U.vr p q) ↔ ∀ i j, (o i = o j → (Y i j).od = 0) ∧ (o i ≠ o j → (Y i j).ev = 0) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hxx, -, -, -, -, hsum, hcor⟩ := units_basic T o U
  have hvr : ∀ w i j, U.vr p q w i j = vrEnt U p q (U.x i * w * T.st (U.x j)) :=
    fun _ _ _ => rfl
  have hrec : ∀ w i j, vrRec U p q (o i) (o j) (U.vr p q w i j) = U.x i * w * T.st (U.x j) := by
    intro w i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).2
  have hx : ∀ i k, U.x i * T.st (U.x k) = if i = k then U.ep (o i) else 0 := by
    intro i k
    split_ifs with h
    · rw [h, U.x_st]
    · exact hxx i k h
  refine ⟨fun w w' h => ?_, fun Y => ⟨?_, ?_⟩⟩
  · rw [hsum w, hsum w']
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← hrec w i j, ← hrec w' i j, h]
  · rintro ⟨w, rfl⟩ i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).1
  · intro hY
    refine ⟨∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l, ?_⟩
    refine Matrix.ext (fun i j => ?_)
    rw [hvr]
    have hr := rec_spec U p q hpq (o i) (o j) (ho i) (ho j) (Y i j) (hY i j)
    have key : U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
        T.st (U.x j) = vrRec U p q (o i) (o j) (Y i j) := by
      calc U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
            T.st (U.x j)
          = ∑ k, ∑ l, (U.x i * T.st (U.x k)) * vrRec U p q (o k) (o l) (Y k l) *
              (U.x l * T.st (U.x j)) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = U.ep (o i) * vrRec U p q (o i) (o j) (Y i j) * U.ep (o j) := by
            simp [hx]
        _ = vrRec U p q (o i) (o j) (Y i j) := hr.1
    rw [key]
    exact hr.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.VrReduction
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.vr_reduction :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) {F : Type} [CommRing F] [Algebra B F] (r : E →ₐ[B] Matrix ι ι F) (p q : ι), (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (o i) i 1) → (∀ y i j, o i ≠ o j → r y i j = 0) → (∀ y i j, algebraMap B F (U.vr p q y i j).ev = r y i j) ∧ (o p = p → o q = q → p ≠ q → (U.oddForm p q).red ≤ RingHom.ker (algebraMap B F)) := by
  intro B E _ _ _ T ι _ _ o U F _ _ r p q hst hx hr
  obtain ⟨-, -, h3, h4, h5, -, h7⟩ := units_basic T o U
  have hep : ∀ k, r (U.ep (o k)) = Matrix.single (o k) (o k) 1 := by
    intro k
    rw [← U.x_base k, hx, U.o_o]
  have hz : ∀ w i j, r (U.x i * w * T.st (U.x j)) = Matrix.single (o i) (o j) (r w i j) := by
    intro w i j
    rw [map_mul, map_mul, hst, hx, hx, Matrix.transpose_single, Matrix.single_mul_mul_single, one_mul, mul_one]
  have key : ∀ w i j, algebraMap B F (T.tr (U.x i * w * T.st (U.x j))) = r w i j := by
    intro w i j
    by_cases hij : o i = o j
    · have e := congrArg (fun M => M (o i) (o j)) (hz w i j)
      simp only [Matrix.single_apply_same] at e
      rw [← e]
      conv_rhs => rw [h5 i j w hij, map_smul, hep i, ← hij]
      simp [Matrix.smul_apply, Algebra.smul_def]
    · rw [hr w i j hij, ← h7 i j w, h3 _ _ _ hij, map_zero]
  refine ⟨fun y i j => ?_, ?_⟩
  · show algebraMap B F (T.tr (U.x i * y * T.st (U.x j))) = _
    exact key y i j
  · intro hp hq hpq
    refine Ideal.span_le.mpr ?_
    rintro c ⟨b, b', rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show algebraMap B F (T.tr ((b : E) * T.st (b' : E))) = 0
    obtain ⟨z, hz'⟩ := b.2
    have hb : r (b : E) = 0 := by
      rw [← hz']
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, map_mul]
      have hpp := hep p
      rw [hp] at hpp
      have hqq := hep q
      rw [hq] at hqq
      rw [hpp, hqq, ← mul_assoc, Matrix.single_mul_mul_single, hr z p q (by rw [hp, hq]; exact hpq)]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h4, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [key, map_mul, hb, zero_mul, Matrix.zero_apply]
end

