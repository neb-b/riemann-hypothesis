module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0229
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineSiteZariskiCoveredByAtlas
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickZar

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem isNilpotent_of_mem_J (hp : b.p ≠ 0) {L : b.Fun} (T : Thick L) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := T.adm.1 hp
  obtain ⟨c, hc⟩ : b.p ∣ b.p.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hp) le_rfl
  refine ⟨b.p * N, ?_⟩
  rw [pow_mul, ← T.δ.factorial_mul_dpow_eq_pow hx, hc, Nat.cast_mul, mul_assoc, mul_pow, hN, zero_mul]

attribute [local instance 1100] Empty.instIsEmpty

def push (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) : Thick (F.cr b ht κ) where
  B := B'
  i := g.comp T.i
  J := T.J.map g
  δ := δ'
  adm := ⟨fun h => by simpa using (T.adm.1 h).map g, fun h => by
    obtain ⟨n, hn⟩ := T.adm.2 h
    exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩⟩
  compat := IsDPMorphism.comp δ' hg T.compat
  α := ()
  y := (F.cr b ht κ).Pt.map (CommRingCat.ofHom (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map)) T.y
  inα := trivial
  w r := by
    rw [(F.cr b ht κ).str_map]
    change (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map) ((F.cr b ht κ).str T.y (Ideal.Quotient.mk _ r)) = _
    rw [T.w]; rfl
  x j := j.elim
  v j := j.elim
  s := Units.map g.toMonoidHom T.s
  hx j := j.elim
  hs := by
    have h := congrArg g T.hs
    have e : ∏ j, T.x j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e, map_one, map_mul] at h
    exact (Finset.prod_of_isEmpty (ι := Empty) _).trans h
  hv := by
    have h := T.hv
    have e : ∏ j, T.v j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e] at h
    refine Eq.trans ?_ (Finset.prod_of_isEmpty (ι := Empty) _).symm
    ext
    have h' := congrArg (fun u : (T.B ⧸ T.J)ˣ => Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map (u : T.B ⧸ T.J)) h
    simpa using h'

def pushHom (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) : T ⟶ push T g δ' hg where
  φ := g
  u j := j.elim
  comm _ := rfl
  dp := hg
  hle := Ideal.le_comap_map
  pt := rfl
  hx j := j.elim
  hs := by
    have e : ∏ j : (F.cr b ht κ).ι, ((j.elim : (push T g δ' hg).Bˣ)) = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e, one_mul]; rfl
  hv j := j.elim

def pushDesc (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) {T'' : Thick (F.cr b ht κ)} (ψ : T ⟶ T'') (χ : B' →+* T''.B) (h : χ.comp g = ψ.φ) :
    push T g δ' hg ⟶ T'' :=
  have hdp : IsDPMorphism δ' T''.δ χ := (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers T.δ g δ' hg).2 T''.δ χ (h ▸ ψ.dp)
  have hle : T.J.map g ≤ T''.J.comap χ := Ideal.map_le_iff_le_comap.1 hdp.1
  have e2 : CommRingCat.ofHom (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map) ≫
      CommRingCat.ofHom (Ideal.quotientMap T''.J χ hle) = CommRingCat.ofHom (Ideal.quotientMap T''.J ψ.φ ψ.hle) := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (χ (g x)) = Ideal.Quotient.mk _ (ψ.φ x)
    rw [← RingHom.comp_apply χ g, h]
  { φ := χ
    u := fun j => j.elim
    comm := fun r => by
      change χ (g (T.i r)) = _
      rw [← RingHom.comp_apply χ g, h]; exact ψ.comm r
    dp := hdp
    hle := hle
    pt := by
      refine Eq.trans ?_ ψ.pt
      change (F.cr b ht κ).Pt.map _ ((F.cr b ht κ).Pt.map _ T.y) = (F.cr b ht κ).Pt.map _ T.y
      rw [← e2, Functor.map_comp]
      rfl
    hx := fun j => j.elim
    hs := by
      have e : ∏ j : (F.cr b ht κ).ι, ((j.elim : T''.Bˣ)) = 1 := Finset.prod_of_isEmpty (ι := Empty) _
      rw [e, one_mul, ψ.hs]
      have e' : ∏ j, ψ.u j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
      rw [e', one_mul]
      ext
      change ψ.φ _ = χ (g _)
      rw [← RingHom.comp_apply χ g, h]
    hv := fun j => j.elim }

theorem hom_ext_cr {T T' : Thick (F.cr b ht κ)} {f g : T ⟶ T'} (h : f.φ = g.φ) : f = g :=
  Thick.Hom.ext h (funext fun j => j.elim)

def locT (T : Thick (F.cr b ht κ)) (a : T.B) : Thick (F.cr b ht κ) :=
  push T (algebraMap T.B (Localization.Away a))
    (Classical.choose (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))

def locHom (T : Thick (F.cr b ht κ)) (a : T.B) : T ⟶ locT T a :=
  pushHom T (algebraMap T.B (Localization.Away a))
    (Classical.choose (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))

theorem locT_univ (T : Thick (F.cr b ht κ)) (a : T.B) {T'' : Thick (F.cr b ht κ)} (ψ : T ⟶ T'')
    (hu : IsUnit (ψ.φ a)) : ∃! χ : locT T a ⟶ T'', locHom T a ≫ χ = ψ := by
  let l : Localization.Away a →+* T''.B := IsLocalization.Away.lift a hu
  have hl : l.comp (algebraMap T.B (Localization.Away a)) = ψ.φ := IsLocalization.Away.lift_comp a hu
  refine ⟨pushDesc T _ _ _ ψ l hl, hom_ext_cr hl, fun χ hχ => hom_ext_cr ?_⟩
  let χ' : Localization.Away a →+* T''.B := χ.φ
  have h1 : χ'.comp (algebraMap T.B (Localization.Away a)) = ψ.φ := congrArg Thick.Hom.φ hχ
  have h2 : χ' = l := IsLocalization.ringHom_ext (Submonoid.powers a) (h1.trans hl.symm)
  exact h2

theorem unit_of_mem (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (S : Finset (Fin m)) {k : Fin m} (hk : k ∈ S) :
    IsUnit ((locHom T (∏ k ∈ S, f k)).φ (f k)) := by
  have h : IsUnit (algebraMap T.B (Localization.Away (∏ k ∈ S, f k)) (∏ k ∈ S, f k)) :=
    IsLocalization.Away.algebraMap_isUnit _
  exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem f hk)) h

theorem pdPow_locT (T : Thick (F.cr b ht κ)) (a : T.B) (r : ℕ) :
    (locT T a).pdPow r = (T.pdPow r).map (algebraMap T.B (Localization.Away a)) :=
  (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers T.δ (algebraMap T.B (Localization.Away a)) _
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))).1 r

theorem loc_surj (T : Thick (F.cr b ht κ)) (a : T.B) (r : ℕ) (y : Localization.Away a)
    (hy : y ∈ (T.pdPow r).map (algebraMap T.B (Localization.Away a))) :
    ∃ (n : ℕ) (x : T.B), x ∈ T.pdPow r ∧
      algebraMap T.B (Localization.Away a) (a ^ n) * y = algebraMap T.B (Localization.Away a) x := by
  obtain ⟨⟨x, s⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers a) _).1 hy
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, x.1, x.2, ?_⟩
  have hn' : a ^ n = s := hn
  rw [mul_comm, hn']
  exact hx

theorem span_lift (hp : b.p ≠ 0) (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (s : Fin m → T.B ⧸ T.J)
    (hf : ∀ k, Ideal.Quotient.mk T.J (f k) = s k) (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range f) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk T.J) (Ideal.span (Set.range f)) = ⊤ := by
    rw [Ideal.map_span, ← Set.range_comp, ← hs]
    congr 2
    exact funext hf
  have h2 : (1 : T.B ⧸ T.J) ∈ Ideal.map (Ideal.Quotient.mk T.J) (Ideal.span (Set.range f)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ T.J := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (isNilpotent_of_mem_J hp T hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

section Mod

variable {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (r : ℕ)

def mulR (T : Thick (F.cr b ht κ)) : T.B →+* Module.End Λ ((pdS (F.cr b ht κ) c r).fn.obj T) where
  toFun a :=
    { toFun := fun x => ⟨(show T.B from a * (show T.B from x.1)), (T.pdPow r).mul_mem_left a x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add a (show T.B from x.1) (show T.B from y.1))
      map_smul' := fun e x => Subtype.ext (mul_left_comm a (T.i (c e)) (show T.B from x.1)) }
  map_one' := LinearMap.ext fun x => Subtype.ext (one_mul (show T.B from x.1))
  map_mul' a a' := LinearMap.ext fun x => Subtype.ext (mul_assoc a a' (show T.B from x.1))
  map_zero' := LinearMap.ext fun x => Subtype.ext (zero_mul (show T.B from x.1))
  map_add' a a' := LinearMap.ext fun x => Subtype.ext (add_mul a a' (show T.B from x.1))

def locMod (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (hf : Ideal.span (Set.range f) = ⊤) :
    LocMod (pdS (F.cr b ht κ) c r).fn T (fun S => locT T (∏ k ∈ S, f k)) (fun S => locHom T (∏ k ∈ S, f k)) where
  Λ := T.B
  f := f
  span := hf
  ρ₀ := mulR c r T
  ρ S := (mulR c r (locT T (∏ k ∈ S, f k))).comp (locHom T (∏ k ∈ S, f k)).φ
  lam_ρ S a x := Subtype.ext (map_mul (locHom T (∏ k ∈ S, f k)).φ a (show T.B from x.1))
  tr_ρ S S' t ht' a x := by
    have e : t.φ.comp (locHom T (∏ k ∈ S, f k)).φ = (locHom T (∏ k ∈ S', f k)).φ := congrArg Thick.Hom.φ ht'
    refine Subtype.ext ?_
    change t.φ ((locHom T (∏ k ∈ S, f k)).φ a * (show (locT T (∏ k ∈ S, f k)).B from x.1)) =
      (locHom T (∏ k ∈ S', f k)).φ a * t.φ (show (locT T (∏ k ∈ S, f k)).B from x.1)
    rw [map_mul, ← RingHom.comp_apply t.φ, e]
  unit S k hk := by
    have hu : IsUnit ((locHom T (∏ k ∈ S, f k)).φ (f k)) := unit_of_mem T f S hk
    obtain ⟨u, hu⟩ := hu
    have hinv : ∀ y : ((pdS (F.cr b ht κ) c r).fn.obj (locT T (∏ k ∈ S, f k))),
        mulR c r _ (↑u : (locT T (∏ k ∈ S, f k)).B) (mulR c r _ (↑u⁻¹ : (locT T (∏ k ∈ S, f k)).B) y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
    have hinv' : ∀ y : ((pdS (F.cr b ht κ) c r).fn.obj (locT T (∏ k ∈ S, f k))),
        mulR c r _ (↑u⁻¹ : (locT T (∏ k ∈ S, f k)).B) (mulR c r _ (↑u : (locT T (∏ k ∈ S, f k)).B) y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    change Function.Bijective (mulR c r _ ((locHom T (∏ k ∈ S, f k)).φ (f k)))
    rw [← hu]
    exact ⟨Function.LeftInverse.injective hinv', Function.RightInverse.surjective hinv⟩
  surj S y := by
    obtain ⟨n, x, hx, e⟩ := loc_surj T (∏ k ∈ S, f k) r y.1 ((pdPow_locT T _ r).le y.2)
    exact ⟨n, ⟨x, hx⟩, Subtype.ext e⟩
  ker S x hx := by
    have h0 : algebraMap T.B (Localization.Away (∏ k ∈ S, f k)) (show T.B from x.1) = 0 := congrArg Subtype.val hx
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (∏ k ∈ S, f k)) _ _).1 h0
    exact ⟨n, Subtype.ext hn⟩

end Mod

theorem zarCov_pdS : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type}
    [CommRing Λ] (c : Λ →+* b.R) {d : ℕ} (𝒜 : F.Atlas d), b.p ≠ 0 → ∀ r : ℕ,
    ZarCov (pdS (F.cr b ht κ) c r).fn fun T => ∃ α, (𝒜.V α).In T.y.1.2 := by
  intro O _ F b ht κ Λ _ c d 𝒜 hp r
  refine ⟨fun T T' φ ⟨α, hα⟩ => ⟨α, ?_⟩, fun T => ?_⟩
  · have h := (𝒜.V α).in_map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) hα
    rw [← φ.pt]
    exact h
  obtain ⟨m, s, hs, hcov⟩ := 𝒜.cov (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2
  choose f hf using fun k => Ideal.Quotient.mk_surjective (s k)
  have hspan : Ideal.span (Set.range f) = ⊤ := span_lift hp T f s hf hs
  refine ⟨m, fun k _ ψ => IsUnit (ψ.φ (f k)), fun k T₁ T₂ ψ χ h => h.map χ.φ, fun k T₁ ψ h => ?_, fun T' φ => ?_⟩
  · have hu : IsUnit ((CommRingCat.ofHom (Ideal.quotientMap T₁.J ψ.φ ψ.hle)).hom (s k)) := by
      rw [← hf k]; exact h.map (Ideal.Quotient.mk T₁.J)
    obtain ⟨α, hα⟩ := hcov k _ _ hu
    refine ⟨α, ?_⟩
    rw [← ψ.pt]
    exact hα
  refine ⟨fun S => locT T' (∏ k ∈ S, φ.φ (f k)), fun S => locHom T' _, fun S k hk => unit_of_mem T' _ S hk,
    fun S T'' ψ h => locT_univ T' _ ψ ?_, ⟨locMod c r T' (fun k => φ.φ (f k)) ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one h
  · have h := congrArg (Ideal.map φ.φ) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h

end GlobalTheory.CompanionTheory.ThickZar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftToThickening
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickHom

theorem isNilpotent_of_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {p : ℕ} (h0 : p ≠ 0)
    (hp : IsNilpotent (p : B)) {x : B} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hp
  have key : ∀ M : ℕ, p ^ M ∣ (M * p).factorial := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Nat.succ_mul, pow_succ]
      exact (mul_dvd_mul ih (Nat.dvd_factorial (Nat.pos_of_ne_zero h0) le_rfl)).trans
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  obtain ⟨c, hc⟩ := key N
  refine ⟨N * p, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hc]
  push_cast
  rw [hN]
  simp

variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I}

theorem comp_eq (T : Thick (F.cr b ht κ)) {g : s.R →+* T.B ⧸ T.J}
    (hg : F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2) (o : O) (x : b.R)
    (hx : Ideal.Quotient.mk b.I x = κ o) : g (s.a o) = Ideal.Quotient.mk T.J (T.i x) := by
  have h1 : F.Ov T.y.1.2 (g.comp s.a) := by
    have := F.ov_map (CommRingCat.ofHom g) s.ov
    rw [hg] at this
    exact this
  have h2 := F.ov_uniq h1 T.y.2
  have h3 := congrArg (fun f : O →+* _ => f o) h2
  have h4 : T.y.1.1 (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk T.J (T.i x) := T.w x
  rw [← h4, hx]
  exact h3

variable (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i))
  (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

attribute [local instance 1100] Empty.instIsEmpty

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

def homOf (T : Thick (F.cr b ht κ)) {g : s.R →+* T.B ⧸ T.J}
    (hg : F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2) (f : 𝓛.D →+* T.B) (hf : f.comp 𝓛.i = T.i)
    (hfg : ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (f z) = g r) :
    liftObj s ht 𝓛 δ hδ hp hn ⟶ T :=
  have hdp : IsDPMorphism δ T.δ f :=
    (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers b.γ 𝓛.i δ hδ).2 T.δ f (by rw [hf]; exact T.compat)
  have hle : b.I.map 𝓛.i ≤ T.J.comap f := Ideal.map_le_iff_le_comap.1 hdp.1
  { φ := f
    u := fun j => j.elim
    comm := fun r => congrArg (fun e : b.R →+* T.B => e r) hf
    dp := hdp
    hle := hle
    pt := by
      have hq : (Ideal.quotientMap T.J f hle).comp 𝓛.j = g := by
        ext r
        obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
        rw [RingHom.comp_apply, ← hz]
        exact hfg r z hz
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        have h1 : T.y.1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T.J (T.i r) := T.w r
        refine Eq.trans ?_ h1.symm
        change Ideal.Quotient.mk T.J (f (𝓛.i r)) = _
        rw [← hf]
        rfl
      · refine Eq.trans ?_ hg
        rw [← hq]
        exact (congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
          (F.Pt.map_comp (CommRingCat.ofHom 𝓛.j) (CommRingCat.ofHom (Ideal.quotientMap T.J f hle)))) s.y₀).symm
    hx := fun j => j.elim
    hs := by
      have : IsEmpty (F.cr b ht κ).ι := inferInstanceAs (IsEmpty Empty)
      have h1 : (liftObj s ht 𝓛 δ hδ hp hn).s = 1 := rfl
      rw [s_eq_one ht T, h1, map_one, Finset.prod_of_isEmpty, one_mul]
    hv := fun j => j.elim }

theorem main (T : Thick (F.cr b ht κ)) :
    ∃ g : s.R →+* T.B ⧸ T.J,
      (∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D),
        Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r) ∧
      F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2 ∧
      ∀ u : Fin d → T.B, (∀ k, Ideal.Quotient.mk T.J (u k) = g (s.T k)) →
        ∃! c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2 (T.y.1.1.comp κ) T.y.2
  have hc : ∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D),
      Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r := by
    intro c r z hz
    have hpt : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T.J c.φ c.hle))
        (F.Pt.map (CommRingCat.ofHom 𝓛.j) s.y₀) = T.y.1.2 := congrArg (fun y => y.1.2) c.pt
    have e := congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
      (F.Pt.map_comp (CommRingCat.ofHom 𝓛.j) (CommRingCat.ofHom (Ideal.quotientMap T.J c.φ c.hle)))) s.y₀
    have hq : (Ideal.quotientMap T.J c.φ c.hle).comp 𝓛.j = g := hgu _ (e.trans hpt)
    have := congrArg (fun e : s.R →+* T.B ⧸ T.J => e r) hq
    refine Eq.trans ?_ this
    exact congrArg (Ideal.quotientMap T.J c.φ c.hle) hz
  refine ⟨g, hc, hg, fun u hu => ?_⟩
  have hJ : EtLift T.J := GlobalTheory.CompanionTheory.EtNil.etLift_of_nil T.J fun x hx =>
    isNilpotent_of_mem T.δ hp (T.adm.1 hp) hx
  obtain ⟨f, ⟨hf1, hf2, hf3⟩, hfu⟩ := GlobalTheory.CompanionTheory.EtaleLift.lift_hom_existsUnique s.a (fun k => (s.T k : s.R)) b.I κ 𝓛
    T.J hJ T.i g u (fun x hx => T.i_mem hx) (comp_eq s ht T hg) hu
  refine ⟨homOf s ht 𝓛 δ hδ hp hn T hg f hf1 hf3, hf2, fun c hck => ?_⟩
  have hcf : c.φ = f := hfu c.φ ⟨RingHom.ext c.comm, hck, hc c⟩
  exact Thick.Hom.ext hcf (funext fun j => j.elim)

end GlobalTheory.CompanionTheory.ThickHom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FlatChartP

open GlobalTheory.CompanionTheory.ChartAlg

theorem flat_of_etale_poly {R D : Type} [CommRing R] [CommRing D] (i : R →+* D) {d : ℕ} (t : Fin d → D)
    (h : (MvPolynomial.eval₂Hom i t : MvPolynomial (Fin d) R →+* D).Etale) : i.Flat := by
  have h1 : (MvPolynomial.eval₂Hom i t : MvPolynomial (Fin d) R →+* D).Flat :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).1
  have h2 : (algebraMap R (MvPolynomial (Fin d) R)).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  have e : i = (MvPolynomial.eval₂Hom i t).comp (algebraMap R (MvPolynomial (Fin d) R)) := by
    ext x
    simp [MvPolynomial.algebraMap_eq]
  rw [e]
  exact RingHom.Flat.comp h2 h1

theorem rep_lift {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (hV : IsAffineOpen V)
    {T : Fin d → Γ(X, V)} (L : CrystallineSemistableComparison.B.Lift (strV q V) T R I κ) (y : PtOver X q κ (L.D ⧸ I.map L.i))
    (h1 : ∀ r, y.1.1 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (L.i r))
    (h2 : y.1.2 = Spec.map (CommRingCat.ofHom L.j) ≫ hV.fromSpec)
    (B : CommRingCat.{0}) (y' : PtOver X q κ B) (hy' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V) :
    ∃! φ : L.D ⧸ I.map L.i →+* B, (ptFun X q κ).map (CommRingCat.ofHom φ) y = y' := by
  let e' : Γ(X, V) →+* B := GlobalTheory.Cris.evalAt y'.1.2 V hy'
  let ψ' : R ⧸ I →+* B := y'.1.1
  have hcomp : ∀ o x, Ideal.Quotient.mk I x = κ o → e' (strV q V o) = (ψ'.comp (Ideal.Quotient.mk I)) x := by
    intro o x hx
    rw [RingHom.comp_apply, hx]
    exact evalAt_base q κ ψ' y'.1.2 y'.2 hy' o
  have hkill : ∀ x ∈ I, (ψ'.comp (Ideal.Quotient.mk I)) x = 0 := fun x hx => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  obtain ⟨f, ⟨hf1, hf2⟩, hu⟩ := L.univ B (ψ'.comp (Ideal.Quotient.mk I)) e' hkill hcomp
  have hJ : ∀ a ∈ I.map L.i, f a = 0 := by
    have : I.map L.i ≤ RingHom.ker f := by
      refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hf1]
      exact hkill x hx
    exact fun a ha => this ha
  let φ : L.D ⧸ I.map L.i →+* B := Ideal.Quotient.lift _ f hJ
  have hφj : φ.comp L.j = e' := by
    refine RingHom.ext fun r => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (L.j r)
    rw [RingHom.comp_apply, ← hz, Ideal.Quotient.lift_mk]
    exact hf2 r z hz
  refine ⟨φ, ?_, fun φ₂ h => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      change φ (y.1.1 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)
      rw [h1, Ideal.Quotient.lift_mk]
      exact RingHom.congr_fun hf1 r
    · change Spec.map (CommRingCat.ofHom φ) ≫ y.1.2 = y'.1.2
      rw [h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφj]
      exact eq_specMap hV _ hy'
  · have a : φ₂.comp y.1.1 = ψ' := congrArg (fun z => z.1.1) h
    have b : Spec.map (CommRingCat.ofHom φ₂) ≫ y.1.2 = y'.1.2 := congrArg (fun z => z.1.2) h
    have e : e' = φ₂.comp L.j := by
      refine evalAt_specMap hV (φ₂.comp L.j) y'.1.2 ?_ hy'
      rw [← b, h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hf : φ₂.comp (Ideal.Quotient.mk _) = f := by
      refine hu _ ⟨?_, fun r z hz => ?_⟩
      · refine RingHom.ext fun r => ?_
        rw [← a, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, h1]
      · rw [RingHom.comp_apply, hz, e]
        rfl
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    rw [hf]
    exact (Ideal.Quotient.lift_mk _ f hJ).symm

theorem exists_flat_chart : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i) := by
  intro O R _ _ I γ p hp hn X q κ V d c
  obtain ⟨L⟩ := GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift (strV q V) c.t I κ c.etale
  have hF : L.i.Flat := flat_of_etale_poly L.i L.t L.et
  obtain ⟨δ, hδ⟩ : ∃ δ : DividedPowers (I.map L.i), IsDPMorphism γ δ L.i := by
    letI : Algebra R L.D := L.i.toAlgebra
    haveI : Module.Flat R L.D := hF
    exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat R L.D I γ
  let ψ : R ⧸ I →+* L.D ⧸ I.map L.i := Ideal.quotientMap _ L.i Ideal.le_comap_map
  have hψ : ∀ r, ψ (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (L.i r) := fun r => rfl
  have hκ : L.j.comp (strV q V) = ψ.comp κ := by
    refine RingHom.ext fun o => ?_
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κ o)
    rw [RingHom.comp_apply, RingHom.comp_apply, L.hj o x hx, ← hx, hψ]
  let y : PtOver X q κ (L.D ⧸ I.map L.i) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom L.j) ≫ c.affine.fromSpec), by
      change (Spec.map (CommRingCat.ofHom L.j) ≫ c.affine.fromSpec) ≫ q = _
      rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ]⟩
  let T : Thick (nlFun γ p X q κ) := mkT L.D L.i (I.map L.i) δ
    ⟨fun _ => by simpa using hn.map L.i, fun h => absurd h hp⟩ hδ y hψ
  have hin : InU V T := top_le_specMap c.affine L.j
  refine ⟨⟨T, L.t, L.et, rfl, hin, fun B y' hy' => rep_lift c.affine L y hψ rfl B y' hy'⟩, hF, fun i => ?_⟩
  have e : ev T hin = L.j := evalAt_specMap c.affine L.j _ rfl hin
  change ev T hin (c.t i) = _
  rw [e]
  exact L.hT i

end GlobalTheory.CompanionTheory.FlatChartP
end
end

