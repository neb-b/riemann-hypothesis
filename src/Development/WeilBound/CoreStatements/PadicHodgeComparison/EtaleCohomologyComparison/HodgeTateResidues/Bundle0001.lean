module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernUnique
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.CmpPutrNe
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Polynomial

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT.Rees

open CH B GlobalTheory.CompanionTheory.ReesDown

section
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {F : D ⥤ ModuleCat.{w} R} (Ψ : Flt F)

def putr (r j : ℕ) (z : Cn (Ψ.S r).fn j) : Cn Ψ.rees j := fun s =>
  show Ψ.Pr _ from Pi.single (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) r (z s)

theorem cmp_putr (r j : ℕ) (z : Cn (Ψ.S r).fn j) : cmp Ψ r j (putr Ψ r j z) = (Ψ.S r).inc.pullC j z :=
  funext fun s => congrArg Subtype.val (Pi.single_eq_same (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) r (z s))

theorem cmp_putr_ne {r r' : ℕ} (h : r' ≠ r) (j : ℕ) (z : Cn (Ψ.S r).fn j) : cmp Ψ r' j (putr Ψ r j z) = 0 :=
  funext fun s => congrArg Subtype.val (Pi.single_eq_of_ne (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) h (z s))

theorem putr_d (r j : ℕ) (z : Cn (Ψ.S r).fn j) : d Ψ.rees j (putr Ψ r j z) = putr Ψ r (j + 1) (d _ j z) := by
  refine cochain_ext Ψ fun r' => ?_
  rw [cmp_d]
  by_cases h : r' = r
  · subst h
    rw [cmp_putr, cmp_putr, Mor.d_pullC]
  · rw [cmp_putr_ne Ψ h, cmp_putr_ne Ψ h, map_zero]

theorem putr_zero (r j : ℕ) : putr Ψ r j 0 = 0 := by
  refine cochain_ext Ψ fun r' => ?_
  by_cases h : r' = r
  · subst h
    rw [cmp_putr, map_zero]; rfl
  · rw [cmp_putr_ne Ψ h]; rfl

theorem putr_mem_B (r j : ℕ) (a : Cn (Ψ.S r).fn j) (h : a ∈ (cx (Ψ.S r).fn).B j) : putr Ψ r j a ∈ (cx Ψ.rees).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this, putr_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨putr Ψ r j e, putr_d Ψ r j e⟩

theorem inc_inj (r j : ℕ) {a b : Cn (Ψ.S r).fn j} (h : (Ψ.S r).inc.pullC j a = (Ψ.S r).inc.pullC j b) : a = b :=
  funext fun s => Subtype.ext (congrFun h s)

theorem inc_cmpS (r j : ℕ) (f : Cn Ψ.rees j) : (Ψ.S r).inc.pullC j (cmpS Ψ r j f) = cmp Ψ r j f := rfl

theorem cmpS_d (r j : ℕ) (f : Cn Ψ.rees j) : cmpS Ψ r (j + 1) (d Ψ.rees j f) = d _ j (cmpS Ψ r j f) :=
  inc_inj Ψ r _ (by rw [inc_cmpS, cmp_d, ← Mor.d_pullC, inc_cmpS])

theorem cmpS_mem_B (r j : ℕ) (a : Cn Ψ.rees j) (h : a ∈ (cx Ψ.rees).B j) : cmpS Ψ r j a ∈ (cx (Ψ.S r).fn).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨cmpS Ψ r j e, (cmpS_d Ψ r j e).symm⟩

theorem cmp_X_pow' (j r k : ℕ) (f : Cn Ψ.rees j) : cmp Ψ (r + k) j ((X : ℤ[X]) ^ k • f) = Ψ.μ ^ k • cmp Ψ r j f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, ← add_assoc, cmp_X, ih, pow_succ', mul_smul]

end

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R}
  (Φ : Flt F) (G : C' ⥤ C) {n N : ℕ}

theorem inj (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees G) {j : ℕ} (hj : j ≤ n) (r : ℕ) (h) (x : H (Φ.S r).fn j)
    (hx : (Mor.restrict (Φ.S r).fn G).pull j x = 0) : (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pull j x = 0 := by
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  obtain ⟨z, hz, rfl⟩ := (P.cls_surj (cx (Φ.S r).fn) j).1 x
  have hpd : d (G ⋙ (Φ.S r).fn) j ((Mor.restrict (Φ.S r).fn G).pullC j z) = 0 := by rw [Mor.d_pullC, hz, map_zero]
  have h2 : (Mor.restrict (Φ.S r).fn G).pullC j z ∈ (cx (G ⋙ (Φ.S r).fn)).B j :=
    ((P.cls_surj (cx (G ⋙ (Φ.S r).fn)) j).2.1 _ hpd).1 hx
  have hZ : d Φ.rees j (putr Φ r j z) = 0 := by
    rw [putr_d, hz]; exact putr_zero Φ r _
  have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j (putr Φ r j z)) = 0 := by
    rw [Mor.d_pullC, hZ, map_zero]
  have h3 : (Mor.restrict Φ.rees G).pull j ((cx Φ.rees).cls _ hZ) = 0 :=
    ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.1 _ hZ').2 (putr_mem_B (Φ.comap G) r j _ h2)
  have hXZ : d Φ.rees j ((X : ℤ[X]) ^ N • putr Φ r j z) = 0 := by
    rw [map_smul, hZ, smul_zero]
  have h4 := hU.1 _ h3
  rw [← (P.cls_surj (cx Φ.rees) j).2.2.2.2 _ _ hZ hXZ] at h4
  have h5 := cmpS_mem_B Φ (r + N) j _ (((P.cls_surj (cx Φ.rees) j).2.1 _ hXZ).1 h4)
  have e : cmpS Φ (r + N) j ((X : ℤ[X]) ^ N • putr Φ r j z) = (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pullC j z :=
    inc_inj Φ _ _ (by rw [inc_cmpS, cmp_X_pow', cmp_putr]; rfl)
  rw [e] at h5
  have hμ : d _ j ((mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pullC j z) = 0 := by rw [Mor.d_pullC, hz, map_zero]
  exact ((P.cls_surj (cx (Φ.S (r + N)).fn) j).2.1 _ hμ).2 h5

theorem surj (h0 : ∀ T, (Φ.S 0).S T = ⊤) (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees G) {j : ℕ} (hj : j ≤ n) (h) (y : H (G ⋙ F) j) :
    ∃ x : H (Φ.S N).fn j, (Mor.restrict (Φ.S N).fn G).pull j x = (mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pull j y := by
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  have h0' : ∀ T, ((Φ.comap G).S 0).S T = ⊤ := fun T => h0 (G.obj T)
  obtain ⟨w, hw, rfl⟩ := (P.cls_surj (cx (G ⋙ F)) j).1 y
  have hW : d (G ⋙ Φ.rees) j (put (Φ.comap G) h0' j w) = 0 := by
    refine (put_d (Φ.comap G) h0' j w).trans ?_
    rw [hw]; exact put_zero (Φ.comap G) h0' _
  obtain ⟨x', hx'⟩ := hU.2 ((cx (G ⋙ Φ.rees)).cls (show (cx (G ⋙ Φ.rees)).X j from put (Φ.comap G) h0' j w) hW)
  obtain ⟨Z, hZ, rfl⟩ := (P.cls_surj (cx Φ.rees) j).1 x'
  have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j Z) = 0 := by
    rw [Mor.d_pullC, hZ, map_zero]
  have hXW : d (G ⋙ Φ.rees) j ((X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) = 0 := by
    rw [map_smul, hW, smul_zero]
  have hx2 := (P.mapH_cls (Mor.restrict Φ.rees G).hom j Z hZ hZ').symm.trans hx'
  rw [← (P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.2.2 _ _ hW hXW] at hx2
  have hB := ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.1 _ _ hZ' hXW).1 hx2
  have hc := cmpS_mem_B (Φ.comap G) N j _ hB
  have e : ∀ A : Cn (Φ.comap G).rees j, A = (Mor.restrict Φ.rees G).pullC j Z →
      cmpS (Φ.comap G) N j (A - (X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) =
        (show Cn ((Φ.comap G).S N).fn j from (Mor.restrict (Φ.S N).fn G).pullC j (cmpS Φ N j Z)) -
          (mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pullC j w := by
    intro A hA
    refine inc_inj (Φ.comap G) _ _ ?_
    rw [inc_cmpS, cmp_sub, cmp_X_pow, cmp_put_zero, hA]
    rfl
  have hc' := (e _ rfl) ▸ hc
  have h1 : d (G ⋙ (Φ.S N).fn) j ((Mor.restrict (Φ.S N).fn G).pullC j (cmpS Φ N j Z)) = 0 := by
    rw [Mor.d_pullC, d_cmpS Φ N j Z hZ, map_zero]
  have h2 : d _ j ((mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pullC j w) = 0 := by rw [Mor.d_pullC, hw, map_zero]
  exact ⟨(cx (Φ.S N).fn).cls _ (d_cmpS Φ N j Z hZ), ((P.cls_surj (cx ((Φ.comap G).S N).fn) j).2.2.1 _ _ h1 h2).2 hc'⟩

def coef {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R)) : Mor (m.G ⋙ F₁) F₂ (RingHom.id R) :=
  ⟨𝟭 _, m.τ, m.nat⟩

theorem coef_bij {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R))
    (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) : Function.Bijective ((coef m).pull j) := by
  have : (coef m).G.IsLeftAdjoint := inferInstanceAs (𝟭 C').IsLeftAdjoint
  exact CrystallineSemistableComparison.P.adj_mor (coef m) h j

theorem coef_res {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R)) (j : ℕ) (x : H F₁ j) :
    m.pull j x = (coef m).pull j ((Mor.restrict F₁ m.G).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

variable {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (hm : ∀ T, Function.Bijective (m.τ T)) (S' : ℕ → SubF F')
  (hS : ∀ r T x, m.τ T x ∈ (S' r).S T → x ∈ (Φ.S r).S (m.G.obj T))

include hm hS in
theorem sub_bij (r : ℕ) (h) (T : C') : Function.Bijective ((subMor m (Φ.S r) (S' r) h).τ T) := by
  refine ⟨fun x y e => Subtype.ext ((hm T).1 (congrArg Subtype.val e)), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (hm T).2 y.1
  exact ⟨⟨x, hS r T x (hx ▸ y.2)⟩, Subtype.ext hx⟩

theorem pow_mem (k r : ℕ) (T : C) (x : F.obj T) (hx : x ∈ (Φ.S r).S T) : Φ.μ ^ k • x ∈ (Φ.S (r + k)).S T := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', mul_smul]; exact Φ.mul _ T _ ih

theorem key {t μ u : R} (ht : t = μ * u) (N : ℕ) {M : Type w} [AddCommGroup M] [Module R M] (a : M) : t ^ N • a = u ^ N • μ ^ N • a := by
  rw [smul_smul, ht, mul_pow, mul_comm]

include hm hS in
theorem inj' (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees m.G) {j : ℕ} (hj : j ≤ n) {t u : R} (ht : t = Φ.μ * u) (r : ℕ) (h h')
    (x : H (Φ.S r).fn j) (hx : (subMor m (Φ.S r) (S' r) h).pull j x = 0) :
    (mulSub (t ^ N) (Φ.S r) (Φ.S (r + N)) h').pull j x = 0 := by
  rw [coef_res] at hx
  have h1 := (coef_bij _ (sub_bij Φ m hm S' hS r h) j).1 (hx.trans (map_zero _).symm)
  have h2 := inj Φ m.G hRI hj r (pow_mem Φ N r) x h1
  have e : (mulSub (t ^ N) (Φ.S r) (Φ.S (r + N)) h').pull j x =
      u ^ N • (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) (pow_mem Φ N r)).pull j x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
    exact key ht N (z.1 s).1
  rw [e, h2, smul_zero]

include hm in
theorem surj' (h0 : ∀ T, (Φ.S 0).S T = ⊤) (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees m.G) {j : ℕ} (hj : j ≤ n) {t u : R}
    (ht : t = Φ.μ * u) (h h') (y : H F' j) :
    ∃ x : H (Φ.S N).fn j, (subMor m (Φ.S N) (S' N) h).pull j x = (mulTo (t ^ N) (S' N) h').pull j y := by
  obtain ⟨y, rfl⟩ := (coef_bij m hm j).2 y
  have hp : ∀ (T : C') (x : (m.G ⋙ F).obj T), Φ.μ ^ N • x ∈ ((Φ.comap m.G).S N).S T := fun T x => by
    have := pow_mem Φ N 0 (m.G.obj T) x (by rw [h0]; trivial)
    rwa [zero_add] at this
  obtain ⟨x, hx⟩ := surj Φ m.G h0 hRI hj hp y
  refine ⟨u ^ N • x, ?_⟩
  rw [map_smul, coef_res]
  refine (congrArg (fun a => u ^ N • (coef (subMor m (Φ.S N) (S' N) h)).pull j a) hx).trans ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  exact (congrArg (u ^ N • ·) (map_smul (m.τ _) (Φ.μ ^ N) (z.1 s))).trans (key ht N _).symm

end CrystallineSemistableComparison.HT.Rees
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EpsTA
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

variable (l : ℕ) [Fact l.Prime]

theorem eps_tA : ∃ (ε : B.Eps l) (u : Acris l), tA l = ε.μ * u := by
  obtain ⟨u, hu, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  exact ⟨GlueBE.eps l, u, by rw [GlueBE.eps_μ]; exact e⟩

theorem tFil : TFil l := fun A n =>
  (eps_tA l).elim fun ε h => h.elim fun u hu => by
    rw [hu, map_mul]
    exact Ideal.mul_mem_right _ _ (ε.μ_mem false A n)

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernCocycleAllLevels
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT

open CH GlobalTheory.EtC E E.Main

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem roots_eq (r r' : Roots l) : r = r' := by
  obtain ⟨ρ, h⟩ := r
  obtain ⟨ρ', h'⟩ := r'
  have : ρ = ρ' := funext fun n => Subtype.ext ((clToC l).injective ((h n).trans (h' n).symm))
  subst this
  rfl

theorem nz (n : ℕ) : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem inv_gb (r : Roots l) (M : Model l K) (n : ℕ) : GlobalTheory.EtC.Inv (l ^ n) (sch.obj (gb M)) :=
  fun U ⟨x⟩ => (Prim.map (show U ⟶ gb M from x).appTop.hom (r.zetaX M n)).2.1

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (hn' : n' = n) (hi' : i' = i) (x : Ht q E n i) :
    (x.cast hn hi).cast hn' hi' = x := by
  subst hn hi
  rfl

theorem eM_rt (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) :
    eM lcNat H r M n i 0 (rootClass i (r.zetaX M n)) = CH.oneH (AcrEl M.P n) :=
  haveI := nz (l := l) n
  GlobalTheory.CompanionTheory.FRootCls.eM_root lcSpec morCup etRoot etIn.gen lcNat H r M n i

theorem one_cup (r : Roots l) (M : Model l K) (n : ℕ) (a : Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0) :
    (cup (l ^ n) (show Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0 from one (l ^ n) (sch.obj (gb M))) a).cast
      (n' := ((0 : ℕ) : ℤ)) (i' := 0) (by omega) (add_zero 0) = a :=
  haveI := nz (l := l) n
  (congrArg (Ht.cast _ _) ((formalIn.a6ring (l ^ n) (sch.obj (gb M))).1 (inv_gb r M n) a)).trans (cast_cast _ _ _ _ a)

theorem eM_one (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))) = CH.oneH (AcrEl M.P n) := by
  have h := fCup etIn lcNat l H r K M n 0 0 0 (add_zero 0) 0 0 0 rfl (one (l ^ n) (sch.obj (gb M))) (rootClass 0 (r.zetaX M n))
  have h1 := congrArg (eM lcNat H r M n 0 0) (one_cup r M n (rootClass 0 (r.zetaX M n)))
  have h2 := congrArg ((mulP (AcrEl M.P n)).cup (add_zero 0) (eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))))) (eM_rt H r M n 0)
  have h3 : (mulP (AcrEl M.P n)).cup (add_zero 0) (eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M)))) (CH.oneH (AcrEl M.P n)) =
      eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))) := cupOne _ _ _ _ _
  exact h3.symm.trans (h2.symm.trans (h.symm.trans (h1.trans (eM_rt H r M n 0))))

theorem one_ex (r : Roots l) (M : Model l K) : ∃ v : M.T 0, ∀ k, v.lev k = one (l ^ k) M.spc :=
  ⟨(⟨fun k => one (l ^ k) (sch.obj (gb M)), fun k =>
      haveI := nz (l := l) (k + 1)
      ((etIn.a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l k.le_succ) _).2.1 (inv_gb r M (k + 1))).1⟩ :
    Hl l (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0), fun _ => rfl⟩

theorem untw_ex (r : Roots l) (M : Model l K) (x : Hl l (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) :
    ∃ v : Hl l (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0,
      ∀ n, v.1 n = GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) n (x.1 n) (rootClass (-1) (r.zetaX M n)) := by
  have hv : ∀ k, red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0
      (GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) (k + 1) (x.1 (k + 1)) (rootClass (-1) (r.zetaX M (k + 1)))) =
      GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k (x.1 k) (rootClass (-1) (r.zetaX M k)) := by
    intro k
    have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1 (x.1 (k + 1)) = x.1 k := x.2 k
    have h2 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1) (rootClass (-1) (r.zetaX M (k + 1))) =
        rootClass (-1) (r.zetaX M k) := (GlobalTheory.CompanionTheory.FRootCls.rootSys etIn.op etIn.red redRoot r M (-1)).2 k
    exact (GlobalTheory.CompanionTheory.FUntwPf.vn_red etIn.a11 _ k _ _).trans (congrArg₂ (GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k) h1 h2)
  exact ⟨⟨fun k => GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k (x.1 k) (rootClass (-1) (r.zetaX M k)), hv⟩, fun _ => rfl⟩

theorem etale_firstChern_exists (M : Model l K) (D : LineData M.X) (r : Roots l) : ∃ v, IsEtaleFirstChernUntwisted r D v :=
  (lineBC (gb M) M.X (pullback.fst _ _ ≫ pullback.fst _ _) D).elim fun D' a => a.elim fun π hD =>
    (lineMap _ D').elim fun L hL =>
      (@chern_class_compatible_system etIn.a2 etIn.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L).2.elim fun x hx =>
        (untw_ex r M x).elim fun v hv =>
          Exists.intro v (Exists.intro D' (Exists.intro π (Exists.intro L (Exists.intro (fun n => x.1 n)
            (And.intro hD (And.intro hL (And.intro hx hv)))))))

theorem firstChern_cocycle_untwisted (H : RIn l) (r : Roots l) (M : Model l K) (D : LineData M.X) (D' : LineData (gb M)) (π : D'.Y ⟶ D.Y)
    (hD : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (L : cech D'.f ⟶ ofCat (glCat 1)) (hL : D'.IsMap L)
    (n : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) (hx : pull _ (cechAug D'.f) _ 2 x = c1 (l ^ n) L)
    (v : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0)
    (hv : v = GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) n x (rootClass (-1) (r.zetaX M n)))
    (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : Lift G D) :
    ∃ (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n (tCo G n 2 z) ∧
      (cx _).cls z hz = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eM lcNat H r M n 0 2 v) :=
  have hI := (@chern_class_compatible_system etIn.a2 etIn.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L).1 n
  have he : eM lcNat H r M n 0 2 v = eM lcNat H r M n 1 2 x :=
    (congrArg (eM lcNat H r M n 0 2) hv).trans
      (GlobalTheory.CompanionTheory.FUntwPf.step fCup cupOne etIn lcNat H r M n x _ (eM_rt H r M n (-1)))
  (E.step etale_chern_class_eq_kummer_class fKum fRes etIn lcNat H r M D D' π hD L hL n hI x hx G Λ).elim fun z c => c.2.elim fun hz e2 =>
    Exists.intro z (Exists.intro hz (And.intro c.1 (res_cls fRes etIn lcNat H r M G n x v he _ e2).symm))

theorem good_eFam (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : (eFam lcNat H r K).Good :=
  ⟨fRed etIn lcNat l H r K, fEqui etIn lcNat l H r K, fPhi lcNat l H r K, fNat etIn lcNat l H r K,
    fun M n i j x y => fCup etIn lcNat l H r K M n 0 0 0 (add_zero 0) i j (i + j) rfl x y,
    fun M => fRoot etIn lcNat l H r K M 0, firstChern_family etIn lcNat l H r K⟩

theorem firstChern_cocycle_all_levels (H : RIn l) (r : Roots l) (M : Model l K) (D : LineData M.X) (v : M.T 2) (h : IsEtaleFirstChernUntwisted r D v)
    (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : Lift G D) (n : ℕ) :
    ∃ (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n (tCo G n 2 z) ∧
      (cx _).cls z hz = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eFam lcNat H r K M n 2 (v.lev n)) :=
  h.elim fun D' h => h.elim fun π h => h.elim fun L h => h.elim fun x h =>
    firstChern_cocycle_untwisted H r M D D' π h.1 L h.2.1 n (x n) (h.2.2.1 n) (v.lev n) (h.2.2.2 n) C G Λ

theorem etP_eFam (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : EtP (eFam lcNat H r K) :=
  ⟨good_eFam H r K, eM_one H r, one_ex r, etale_firstChern_exists,
    fun M D r' v h C _ G Λ n =>
      firstChern_cocycle_all_levels H r M D v (roots_eq r' r ▸ h) C G Λ n⟩

theorem etP (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : ∃ e : E.EtFam l K, EtP e :=
  (rootsEx l).elim fun r => ⟨_, etP_eFam (CrystallineSemistableComparison.R.forE l) r K⟩

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsLiftOneSOfLevEqOne
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open CH PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']

theorem subMor_cup {A : C ⥤ CommAlgCat.{0} R} {A' : C' ⥤ CommAlgCat.{0} R'} (m : CH.Mor (modF A) (modF A') σ)
    (hm : ∀ (T : C') (x y : A.obj (m.G.obj T)), m.τ T (x * y) = (show A'.obj T from m.τ T x) * (show A'.obj T from m.τ T y))
    {S₁ S₂ S₃ : SubF (modF A)} {S₁' S₂' S₃' : SubF (modF A')} (h₁ h₂ h₃) (hS hS') {p q n : ℕ} (h : p + q = n)
    (x : H S₁.fn p) (y : H S₂.fn q) :
    (subMor m S₃ S₃' h₃).pull n ((subPair S₁ S₂ S₃ hS).cup h x y) =
      (subPair S₁' S₂' S₃' hS').cup h ((subMor m S₁ S₁' h₁).pull p x) ((subMor m S₂ S₂' h₂).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (subPair S₁ S₂ S₃ hS) (subPair S₁' S₂' S₃' hS') m.G (subMor m S₁ S₁' h₁).τ (subMor m S₂ S₂' h₂).τ
    (subMor m S₃ S₃' h₃).τ (subMor m S₁ S₁' h₁).nat (subMor m S₂ S₂' h₂).nat (subMor m S₃ S₃' h₃).nat
    (fun T x y => Subtype.ext (hm T _ _)) h x y

theorem mulTo_cup {A : C ⥤ CommAlgCat.{0} R} {c₁ c₂ c₃ : R} (hc : c₃ = c₁ * c₂) {S₁ S₂ S₃ : SubF (modF A)} (h₁ h₂ h₃) (hS)
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    (mulTo c₃ S₃ h₃).pull n ((mulP A).cup h x y) =
      (subPair S₁ S₂ S₃ hS).cup h ((mulTo c₁ S₁ h₁).pull p x) ((mulTo c₂ S₂ h₂).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (subPair S₁ S₂ S₃ hS) (𝟭 C) (mulTo c₁ S₁ h₁).τ (mulTo c₂ S₂ h₂).τ
    (mulTo c₃ S₃ h₃).τ (mulTo c₁ S₁ h₁).nat (mulTo c₂ S₂ h₂).nat (mulTo c₃ S₃ h₃).nat
    (fun T (x y : A.obj T) => Subtype.ext (show c₃ • (x * y) = (c₁ • x) * (c₂ • y) by rw [hc, smul_mul_smul_comm])) h x y

theorem subMor_one {A : C ⥤ CommAlgCat.{0} R} {A' : C' ⥤ CommAlgCat.{0} R'} (m : CH.Mor (modF A) (modF A') σ)
    (hm : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) {c : R} {c' : R'} (hc : c = 1) (hc' : c' = 1)
    {S : SubF (modF A)} {S' : SubF (modF A')} (h h₁ h₂) :
    (subMor m S S' h).pull 0 ((mulTo c S h₁).pull 0 (CH.oneH A)) = (mulTo c' S' h₂).pull 0 (CH.oneH A') := by
  subst hc hc'
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ ((1 : R) • (1 : A.obj _)) = (1 : R') • (1 : A'.obj _)
  rw [one_smul, one_smul, hm]

end Gen

section Pd
variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}
  {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (hσ : ∀ a, σ (c a) = c' (σ₀ a))

theorem pdOm_cup {r r' s : ℕ} (e : r + r' = s) {p q n : ℕ} (h : p + q = n) (x : H (B.pdS L c r).fn p) (y : H (B.pdS L c r').fn q) :
    (pdOm m σ₀ hσ s).pull n ((pdPair L c e).cup h x y) =
      (pdPair L' c' e).cup h ((pdOm m σ₀ hσ r).pull p x) ((pdOm m σ₀ hσ r').pull q y) :=
  subMor_cup (A := B.OA L c) (A' := B.OA L' c') (B.omMor m σ₀ hσ) (fun _ _ _ => rfl) _ _ _ _ _ h x y

theorem pdOm_one : (pdOm m σ₀ hσ 0).pull 0 (pdOne L c) = pdOne L' c' :=
  subMor_one (A := B.OA L c) (A' := B.OA L' c') (B.omMor m σ₀ hσ) (fun _ => rfl) rfl rfl _ _ _

end Pd

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def ttPair (P : PAlg l ⥤ Type) (n : ℕ) {r r' s : ℕ} (h : r + r' = s) : Pairing (TT P r n).fn (TT P r' n).fn (TT P s n).fn :=
  subPair (A := AcrEl P n) (TT P r n) (TT P r' n) (TT P s n) fun T x y hx hy =>
    mem_TT.2 (h ▸ dividedPowerFiltration_mul (B.DD false T.1.obj n) r r' (mem_TT.1 hx) (mem_TT.1 hy))

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem βF_cup (n : ℕ) {r r' s : ℕ} (e : r + r' = s) {p q k : ℕ} (h : p + q = k)
    (x : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn p) (y : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r').fn q) :
    (βMorF F κ s n).pull k ((pdPair (B.Lc F κ false n) ((base l).cris n) e).cup h x y) =
      (ttPair (F.pt κ) n e).cup h ((βMorF F κ r n).pull p x) ((βMorF F κ r' n).pull q y) :=
  subMor_cup (A := B.OcA F κ false n) (A' := AcrEl (F.pt κ) n) (B.βMor F κ false n) (fun _ _ _ => rfl) _ _ _ _ _ h x y

theorem βF_one (ht : TFil l) (n : ℕ) : (βMorF F κ 0 n).pull 0 (pdOne (B.Lc F κ false n) ((base l).cris n)) =
    (tMor ht (F.pt κ) 0 n).pull 0 (CH.oneH (AcrEl (F.pt κ) n)) :=
  subMor_one (A := B.OcA F κ false n) (A' := AcrEl (F.pt κ) n) (B.βMor F κ false n) (fun _ => rfl) rfl (pow_zero _) _ _ _

end F

theorem tMor_cup (ht : TFil l) (P : PAlg l ⥤ Type) (n : ℕ) {r r' s : ℕ} (e : r + r' = s) {p q k : ℕ} (h : p + q = k)
    (x : MH P n p) (y : MH P n q) :
    (tMor ht P s n).pull k ((mulP (AcrEl P n)).cup h x y) =
      (ttPair P n e).cup h ((tMor ht P r n).pull p x) ((tMor ht P r' n).pull q y) :=
  mulTo_cup (A := AcrEl P n) (by rw [← e, pow_add]) _ _ _ _ h x y

theorem comp_cup {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {x : Fam M r i} {y : Fam M r' j} (hx : Comp x) (hy : Comp y) :
    Comp (cupS h x y) := fun n =>
  (pdOm_cup (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ) h rfl
    (x (n + 1)) (y (n + 1))).trans
    (congrArg₂ ((pdPair (M.L false n) ((base l).cris n) h).cup rfl) (hx n) (hy n))

theorem comp_one (M : Model l K) : Comp (oneS M) := fun n =>
  pdOm_one (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ)

theorem cup_gen (ht : TFil l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (n : ℕ) {r r' s i j : ℕ} (e : r + r' = s)
    (x : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn i) (y : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r').fn j)
    (a : MH (F.pt κ) n i) (b : MH (F.pt κ) n j) (w : MH (F.pt κ) n (i + j))
    (hw : w = (mulP (AcrEl (F.pt κ) n)).cup rfl a b)
    (hx : (βMorF F κ r n).pull i x = (tMor ht (F.pt κ) r n).pull i a)
    (hy : (βMorF F κ r' n).pull j y = (tMor ht (F.pt κ) r' n).pull j b) :
    (βMorF F κ s n).pull (i + j) ((pdPair (B.Lc F κ false n) ((base l).cris n) e).cup rfl x y) =
      (tMor ht (F.pt κ) s n).pull (i + j) w :=
  ((βF_cup F κ n e rfl x y).trans (congrArg₂ ((ttPair (F.pt κ) n e).cup rfl) hx hy)).trans
    ((tMor_cup ht (F.pt κ) n e rfl a b).symm.trans (congrArg ((tMor ht (F.pt κ) s n).pull (i + j)) hw.symm))

variable (ht : TFil l) {e : E.EtFam l K}

theorem isLift_cupS_of_cupT (he : EtP e) : ∀ {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {v : M.T i} {v' : M.T j} {w : M.T (i + j)}
    {x : Fam M r i} {x' : Fam M r' j}, M.CupT v v' w → IsLift ht e r v x → IsLift ht e r' v' x' → IsLift ht e s w (cupS h x x') :=
  fun {M _ _ _ i j} h {v v' w x x'} hw hx hx' => ⟨comp_cup h hx.1 hx'.1, fun n =>
    cup_gen ht (B.schFn M.p) (okToOC l K) n h (x n) (x' n) (e M n i (v.lev n)) (e M n j (v'.lev n)) (e M n (i + j) (w.lev n))
      ((congrArg (e M n (i + j)) (hw n)).trans (he.good.cup M n i j (v.lev n) (v'.lev n))) (hx.2 n) (hx'.2 n)⟩

theorem isLift_oneS_of_lev_eq_one (he : EtP e) : ∀ (M : Model l K) (v : M.T 0), (∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) →
    IsLift ht e 0 v (oneS M) := fun M v hv => ⟨comp_one M, fun n =>
  (βF_one (B.schFn M.p) (okToOC l K) ht n).trans
    (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) 0 n).pull 0) ((congrArg (e M n 0) (hv n)).trans (he.one M n)).symm)⟩

end CrystallineSemistableComparison.HT
end
end

