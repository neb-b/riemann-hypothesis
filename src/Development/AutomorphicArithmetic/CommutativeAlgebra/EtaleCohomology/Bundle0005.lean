module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GFaceSnGCastSucc
public import Development.AutomorphicArithmetic.EtaleIdempotents.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Polynomial CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

section Factor

variable {R : Type} [CommRing R] {e : R}

private abbrev factorMk (e : R) : R →+* R ⧸ Ideal.span {1 - e} :=
  Ideal.Quotient.mk _

private theorem mk_eq_iff (he : IsIdempotentElem e) (a b : R) :
    factorMk e a = factorMk e b ↔ e * a = e * b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    linear_combination e * hc - c * he.eq
  · intro h
    exact ⟨a - b, by linear_combination h⟩

private theorem mk_self (he : IsIdempotentElem e) : factorMk e e = 1 := by
  rw [← map_one (factorMk e), mk_eq_iff he, mul_one, he.eq]

private theorem dvd_of_mk_dvd (he : IsIdempotentElem e) {a b : R} (h : factorMk e a ∣ factorMk e b) : a ∣ e * b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, mk_eq_iff he] at hc
  exact ⟨e * c, by linear_combination hc⟩

private theorem mem_pow_iff {S : Type} [CommRing S] (a x : S) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule S S) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem perfect_quot (he : IsIdempotentElem e) {p : ℕ} (hp : 0 < p) [PerfectRing R p] :
    PerfectRing (R ⧸ Ideal.span {1 - e}) p := by
  have hep : e ^ p = e := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    exact he.pow_succ_eq k
  have hb := PerfectRing.bijective_frobenius (R := R) (p := p)
  refine ⟨⟨fun x y h => ?_, fun x => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h' : factorMk e (a ^ p) = factorMk e (b ^ p) := by simpa only [map_pow] using h
    rw [mk_eq_iff he] at h' ⊢
    apply hb.1
    show (e * a) ^ p = (e * b) ^ p
    rw [mul_pow, mul_pow, hep, h']
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb'⟩ := hb.2 a
    exact ⟨factorMk e b, by rw [← hb']; simp only [map_pow]⟩

private theorem nzd_quot (he : IsIdempotentElem e) {π : R} (h : π ∈ nonZeroDivisors R) :
    factorMk e π ∈ nonZeroDivisors (R ⧸ Ideal.span {1 - e}) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, ← map_zero (factorMk e), mk_eq_iff he, mul_zero] at hx
  rw [← map_zero (factorMk e), mk_eq_iff he, mul_zero]
  rw [mem_nonZeroDivisors_iff_right] at h
  exact h _ (by linear_combination hx)

private theorem complete_quot (he : IsIdempotentElem e) {π : R} (h : IsAdicComplete (Ideal.span {π}) R) :
    IsAdicComplete (Ideal.span {factorMk e π}) (R ⧸ Ideal.span {1 - e}) := by
  have hH := h.toIsHausdorff
  have hP := h.toIsPrecomplete
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_zero (factorMk e), mk_eq_iff he, mul_zero]
    refine hH.haus' _ fun n => ?_
    rw [SModEq.zero, mem_pow_iff]
    have := (hx n)
    rw [SModEq.zero, mem_pow_iff, ← map_pow] at this
    exact dvd_of_mk_dvd he this
  · choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)
    obtain ⟨L, hL⟩ := hP.prec' (fun n => e * g n) (fun {m n} hmn => by
      have := hf hmn
      rw [SModEq.sub_mem, mem_pow_iff, ← map_pow, ← hg m, ← hg n, ← map_sub] at this
      rw [SModEq.sub_mem, mem_pow_iff]
      have h2 := dvd_of_mk_dvd he this
      rwa [mul_sub] at h2)
    refine ⟨factorMk e L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem, mem_pow_iff] at this ⊢
    have h3 := map_dvd (factorMk e) this
    rw [map_pow, map_sub, map_mul, mk_self he, one_mul, hg n] at h3
    exact h3

private theorem aic_quot (I : Ideal R) (h : ∀ P : R[X], P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x) :
    ∀ P : (R ⧸ I)[X], P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x := by
  intro P hP hd
  have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective P)
  obtain ⟨q, rfl, hdeg, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
  obtain ⟨x, hx⟩ := h q hq (hdeg ▸ hd)
  exact ⟨_, hx.map (Ideal.Quotient.mk I)⟩

private theorem val_quot (he : IsIdempotentElem e) {π : R}
    (h : ∀ f g : R, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ u : R, IsIdempotentElem u ∧ u * f ∈ Ideal.span {g} ∧ (1 - u) * g ∈ Ideal.span {f}) :
    ∀ f g : R ⧸ Ideal.span {1 - e}, (∃ N : ℕ, factorMk e π ^ N ∈ Ideal.span {f, g}) →
      ∃ u : R ⧸ Ideal.span {1 - e}, IsIdempotentElem u ∧ u * f ∈ Ideal.span {g} ∧ (1 - u) * g ∈ Ideal.span {f} := by
  intro f g ⟨N, hN⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨c', d', hcd⟩ := Ideal.mem_span_pair.1 hN
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d'
  have hE : e * (c * a + d * b) = e * π ^ N := by
    rw [← mk_eq_iff he]
    simpa only [map_add (f := _), map_mul, map_pow] using hcd
  obtain ⟨u, hu, h1, h2⟩ := h (a * e + (1 - e)) (b * e) ⟨N, Ideal.mem_span_pair.2
    ⟨c * e + π ^ N * (1 - e), d, by
      linear_combination hE + (c * a - c - π ^ N * a + π ^ N) * he.eq⟩⟩
  have hm : factorMk e (1 - e) = 0 := by rw [map_sub, map_one, mk_self he, sub_self]
  have ha : factorMk e (a * e + (1 - e)) = factorMk e a := by
    rw [map_add (f := _), map_mul, mk_self he, hm, mul_one, add_zero]
  have hb : factorMk e (b * e) = factorMk e b := by rw [map_mul, mk_self he, mul_one]
  rw [Ideal.mem_span_singleton] at h1 h2
  refine ⟨factorMk e u, ?_, ?_, ?_⟩
  · show factorMk e u * factorMk e u = factorMk e u
    rw [← map_mul, hu.eq]
  · rw [Ideal.mem_span_singleton]
    have := map_dvd (factorMk e) h1
    rwa [hb, map_mul, ha] at this
  · rw [Ideal.mem_span_singleton]
    have := map_dvd (factorMk e) h2
    rwa [ha, map_mul, hb, map_sub, map_one] at this

end Factor

variable {l : ℕ} [Fact l.Prime]

private def factor (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) : PAlg l where
  A := A.A ⧸ Ideal.span {1 - e}
  s := (Ideal.Quotient.mk _).comp A.s
  perf := perfect_quot he (Fact.out : l.Prime).pos
  compl := complete_quot he A.compl
  tf := nzd_quot he A.tf

private theorem factor_isTest (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) (h : A.IsTest) :
    (factor A he).IsTest :=
  ⟨aic_quot _ h.1, val_quot he h.2⟩

theorem decEx : DecEx := by
  intro l _ A ι _ e he
  refine ⟨fun i => ⟨factor A.obj (he.idem i), factor_isTest _ _ A.property⟩,
    fun i => ObjectProperty.homMk ⟨Ideal.Quotient.mk _, rfl⟩, ?_, fun i => ?_⟩
  · exact he.bijective_pi
  · exact mk_self (he.idem i)

end UpperTheory.Ru.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NatCastQb
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open PAlg

variable {l : ℕ} [Fact l.Prime]

private theorem natCast_qb (A : PAlg l) : (l : Qb A) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {A.s (pFlat l)})), A.natCast_l, map_zero]

private def frQ (A : PAlg l) : Qb A →+* Qb A where
  toFun x := x ^ l
  map_one' := one_pow _
  map_mul' x y := mul_pow x y l
  map_zero' := zero_pow (Fact.out : l.Prime).ne_zero
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) x y
    rw [hr, natCast_qb A]; simp

private def pw (A : PAlg l) : ℕ → (Qb A →+* Qb A)
  | 0 => RingHom.id _
  | m + 1 => (frQ A).comp (pw A m)

private theorem pw_apply (A : PAlg l) (m : ℕ) (x : Qb A) : pw A m x = x ^ l ^ m := by
  induction m with
  | zero => simp [pw]
  | succ m ih =>
    change (pw A m x) ^ l = _
    rw [ih, ← pow_mul, pow_succ]

private theorem mapQ_pw {A B : PAlg l} (f : A ⟶ B) (m : ℕ) (x : Qb A) :
    PAlg.mapQ f (pFlat l) (pw A m x) = pw B m (PAlg.mapQ f (pFlat l) x) := by
  rw [pw_apply, pw_apply, map_pow]

private theorem coeff_xi (A : PAlg l) : A.xi.coeff 0 = - A.s (pFlat l) := by
  have h : (xi0 l).coeff 0 = - pFlat l := by
    change WittVector.constantCoeff (xi0 l) = _
    rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    congr 1
  change (WittVector.map A.s (xi0 l)).coeff 0 = _
  rw [WittVector.map_coeff, h, map_neg]

private def rd (A : PAlg l) (m : ℕ) : A.U →+* Qb A :=
  Ideal.Quotient.lift _ ((pw A m).comp ((Ideal.Quotient.mk _).comp WittVector.constantCoeff)) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have h0 : (Ideal.Quotient.mk (Ideal.span {A.s (pFlat l)})) (WittVector.constantCoeff A.xi) = 0 := by
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      change A.xi.coeff 0 ∈ _
      rw [coeff_xi]
      exact neg_mem (Ideal.mem_span_singleton_self _)
    simp only [RingHom.comp_apply, map_mul, h0, mul_zero, map_zero]

private theorem rd_th (A : PAlg l) (m : ℕ) (x : A.W) :
    rd A m (A.th x) = Ideal.Quotient.mk _ (x.coeff 0) ^ l ^ m :=
  pw_apply A m _

private theorem rd_ext (A : PAlg l) (m : ℕ) (ψ : A.U →+* Qb A)
    (h : ∀ x : A.W, ψ (A.th x) = Ideal.Quotient.mk _ (x.coeff 0) ^ l ^ m) : ψ = rd A m :=
  RingHom.ext fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (h y).trans (rd_th A m y).symm

private theorem rd_mapU {A B : PAlg l} (f : A ⟶ B) (m : ℕ) (x : A.U) :
    rd B m (mapU f x) = PAlg.mapQ f (pFlat l) (rd A m x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change rd B m (B.th (mapW f y)) = PAlg.mapQ f (pFlat l) (rd A m (A.th y))
  rw [rd_th, rd_th, map_pow]
  congr 1

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

private def frT (f : ℕ) {g : O →+* Qo l} (hg : ∀ x, g x ^ l ^ f = g x) : PQ q g ⟶ PQ q g where
  app A := TypeCat.ofHom fun y => ⟨Spec.map (CommRingCat.ofHom (pw A f)) ≫ y.1, by
    rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply]
    rw [pw_apply, ← map_pow, hg]⟩
  naturality A B φ := by
    ext y
    refine Subtype.ext ?_
    change Spec.map (CommRingCat.ofHom (pw B f)) ≫ Spec.map (CommRingCat.ofHom (PAlg.mapQ φ (pFlat l))) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (PAlg.mapQ φ (pFlat l))) ≫ Spec.map (CommRingCat.ofHom (pw A f)) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun x => (mapQ_pw φ f x).symm

private def rdT (m : ℕ) {κ : O →+* OC l} {g : O →+* Qo l}
    (hg : ∀ (x : O) (w : Ainf l), theta0 l w = κ x → g x = Ideal.Quotient.mk _ (w.coeff 0) ^ l ^ m) :
    PX q κ ⟶ PQ q g where
  app A := TypeCat.ofHom fun y => ⟨Spec.map (CommRingCat.ofHom (rd A m)) ≫ y.1, by
    rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (κ x)
    simp only [RingHom.comp_apply]
    rw [← hw, oC_theta0, rd_th, hg x w hw, map_pow]
    congr 1⟩
  naturality A B φ := by
    ext y
    refine Subtype.ext ?_
    change Spec.map (CommRingCat.ofHom (rd B m)) ≫ Spec.map (CommRingCat.ofHom (mapU φ)) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (PAlg.mapQ φ (pFlat l))) ≫ Spec.map (CommRingCat.ofHom (rd A m)) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun x => (rd_mapU φ m x)

private theorem pull_sq {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {σ : R →+* R} (a : CH.Mor F F σ) (a' : CH.Mor F' F' σ)
    (b : CH.Mor F F' (RingHom.id R)) (j : ℕ)
    (h : ∀ c : CH.Cn F j, a'.pullC j (b.pullC j c) = b.pullC j (a.pullC j c)) (x : CH.H F j) :
    a'.pull j (b.pull j x) = b.pull j (a.pull j x) := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((CH.cx F').B j).submoduleOf ((CH.cx F').Z j))) (Subtype.ext (h c.1))

private theorem phi_pull {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (n j : ℕ) (x : MH P' n j) :
    phiH P n j (pullH u n j x) = pullH u n j (phiH P' n j x) :=
  pull_sq (phiMor P' n) (phiMor P n) (pullMor u n) j (fun c => funext fun s => rfl) x

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.frEx :
    UpperTheory.Ru.crystallineComparison.FrEx := by
  intro l _ O _ X q κ g m f hg
  refine ⟨⟨frT f hg, fun A φ hφ y => ?_⟩, fun h => ⟨rdT m h, fun A ψ hψ y => ?_⟩, fun P P' u n j x => phi_pull u n j x⟩
  · have e : φ = pw A f := RingHom.ext fun x => (hφ x).trans (pw_apply A f x).symm
    rw [e]; rfl
  · rw [rd_ext A m ψ hψ]; rfl
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TheoryEx
section
theorem UpperTheory.Ru.crystallineComparison.theoryEx :
    UpperTheory.Ru.crystallineComparison.TheoryEx := by
  intro C _
  obtain ⟨z, hz₁, hz₂⟩ := UpperTheory.exists_cohomology_zero_equiv_sections_natural C
  refine ⟨{ H := UpperTheory.Ru.crystallineComparison.Th.TH
            ab := fun _ _ _ => inferInstance
            pull := fun u F j => UpperTheory.Ru.crystallineComparison.Th.tPull u F j
            map := fun P _ _ α j => UpperTheory.Ru.crystallineComparison.Th.tMap P α j
            pull_map := fun u _ _ α j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tMap u α j x
            δ := UpperTheory.Ru.crystallineComparison.Th.tδ
            pull_δ := fun u S h j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tδ u S h j x
            ex₃ := UpperTheory.Ru.crystallineComparison.Th.ex₃
            ex₁ := UpperTheory.Ru.crystallineComparison.Th.ex₁
            zero := z
            zero_pull := hz₁
            zero_map := hz₂
            inj := UpperTheory.Ru.crystallineComparison.Th.vanish }, fun R _ F => ?_⟩
  obtain ⟨F', c, e, h₁, h₂⟩ := UpperTheory.exists_coefficient_equiv_cohomology_of_elements C R F
  exact ⟨F', c, e, h₁, h₂⟩
end

