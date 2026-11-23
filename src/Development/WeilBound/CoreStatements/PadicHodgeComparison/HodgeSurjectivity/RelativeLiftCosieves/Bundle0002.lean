module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.AffRelOf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

universe w w' w''

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace AffineRelativeForms

section Abstract

variable {R : Type} [CommRing R]

theorem les_one {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (f : Cx.Hom K L (RingHom.id R))
    (g : Cx.Hom L M (RingHom.id R)) (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n)) (a : ℕ) (hL : ∀ j, j ≠ a → Subsingleton (L.H j))
    (hM : ∀ j, j ≠ a → Subsingleton (M.H j)) (hga : Function.Surjective (g.mapH a)) :
    (∀ j, j ≠ a → Subsingleton (K.H j)) ∧ Function.Injective (f.mapH a) ∧
      ∀ x, x ∈ Set.range (f.mapH a) ↔ g.mapH a x = 0 := by
  obtain ⟨δ, -, h0, hfg', hgδ, hδf⟩ := CrystallineSemistableComparison.P.les f g hf hfg hg
  refine ⟨fun j hj => ?_, ?_, fun x => (hfg' a x).symm⟩
  · suffices h : ∀ x : K.H j, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
    intro x
    have hx : f.mapH j x = 0 := by
      have := hL j hj
      exact Subsingleton.elim _ _
    cases j with
    | zero => exact h0 (by rw [hx, map_zero])
    | succ k =>
      obtain ⟨y, rfl⟩ := (hδf k x).1 hx
      by_cases hk : k = a
      · subst hk
        obtain ⟨z, rfl⟩ := hga y
        exact (hgδ k _).2 ⟨z, rfl⟩
      · have := hM k hk
        rw [Subsingleton.elim y 0, map_zero]
  · cases a with
    | zero => exact h0
    | succ k =>
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := (hδf k x).1 hx
      have := hM k (by omega)
      rw [Subsingleton.elim y 0, map_zero]

end Abstract

section Ses

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
  (U Q : ObjectProperty C)

def liftQ (hQ : Cosieve Q) {n : ℕ} (s : ComposableArrows U.FullSubcategory n) (hs : Q (s.obj 0).obj) :
    ComposableArrows (U ⊓ Q).FullSubcategory n :=
  ObjectProperty.lift (U ⊓ Q) (s ⋙ U.ι) fun j =>
    show U (s.obj j).obj ∧ Q (s.obj j).obj from ⟨(s.obj j).property, hQ (s.map (homOfLE (Fin.zero_le j))).hom hs⟩

theorem res_surj (hQ : Cosieve Q) (hle : U ⊓ Q ≤ U) (n : ℕ) : Function.Surjective ((resU F hle).pullC n) := by
  classical
  intro z
  refine ⟨fun s => if hs : Q (s.obj 0).obj then z (liftQ U Q hQ s hs) else 0, ?_⟩
  funext s
  have hs : Q ((s ⋙ ObjectProperty.ιOfLE hle).obj 0).obj := (s.obj 0).property.2
  change (if hs : Q ((s ⋙ ObjectProperty.ιOfLE hle).obj 0).obj then z (liftQ U Q hQ _ hs) else 0) = z s
  rw [dite_eq_left hs]
  rfl

theorem res_exact (hQ : Cosieve Q) (hle : U ⊓ Q ≤ U) (ι : Cx.Hom (RC F U hQ) (CH.cx (U.ι ⋙ F)) (RingHom.id R))
    (hι : ∀ n x, ι.f n x = x.1) (n : ℕ) : Function.Exact (ι.f n) ((resU F hle).pullC n) := by
  intro y
  constructor
  · intro hy
    refine ⟨⟨y, fun s hs => ?_⟩, hι n _⟩
    exact congrFun hy (liftQ U Q hQ s hs)
  · rintro ⟨x, rfl⟩
    rw [hι]
    funext s
    exact x.2 (s ⋙ ObjectProperty.ιOfLE hle) (s.obj 0).property.2

end Ses

end AffineRelativeForms

open AffineRelativeForms in
theorem affRelOf_pf : AffRelOf := by
  intro hSite hOn hAff hNat hForm K _ _ W Z q i _ hQ V d d' hc hc' a
  have : Mono i := inferInstance
  have hS := hSite K W Z W q i i
  have h0 : ∀ T, inU (i ≫ q) (i ⁻¹ᵁ V) T → inU q V ((smS i rfl).G.obj T) := fun T h => (hS.2.2.2.2.1 V T).1 h
  have h2 : ∀ T, inU q V ((smS i rfl).G.obj T) → inU (i ≫ q) (i ⁻¹ᵁ V) T := fun T h => (hS.2.2.2.2.1 V T).2 h
  have hOnW : ∀ T, On q i ((smS i rfl).G.obj T) := by
    intro T
    refine (hS.2.2.2.2.2 T).1 ?_
    obtain ⟨w, hw⟩ : ∃ w, w = pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T := ⟨_, rfl⟩
    exact ⟨pullback.lift w w rfl, by rw [pullback.lift_snd, hw]⟩
  have h1 : ∀ T, inU (i ≫ q) (i ⁻¹ᵁ V) T → (inU q V ⊓ On q i) ((smS i rfl).G.obj T) :=
    fun T h => show inU q V _ ∧ On q i _ from ⟨h0 T h, hOnW T⟩
  have hBij := hOn K W Z q i (inU q V) (inU (i ≫ q) (i ⁻¹ᵁ V)) h1 h2 a
  obtain ⟨hVsub, e0, he0, he0b⟩ := hAff K Z q V d hc a
  obtain ⟨hWsub, e', he', he'b⟩ := hAff K W (i ≫ q) (i ⁻¹ᵁ V) d' hc' a
  obtain ⟨φ, hφ, hnat⟩ := hNat K Z W q (i ≫ q) i rfl V (i ⁻¹ᵁ V) le_rfl h0
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := i.app_surjective V hc.some.affine y
    exact ⟨x, by rw [hφ, Scheme.Hom.appLE_eq_app]; exact hx⟩
  have hFL := ((hForm K (Sec q V) (Sec (i ≫ q) (i ⁻¹ᵁ V)) a).2 φ).2.2 hφs
  have hker : RingHom.ker φ = (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) := by
    ext g
    show g ∈ RingHom.ker φ ↔ g ∈ RingHom.ker (i.app V).hom
    rw [RingHom.mem_ker, RingHom.mem_ker, hφ, Scheme.Hom.appLE_eq_app]
    exact Iff.rfl
  have hle : inU q V ⊓ On q i ≤ inU q V := fun T h => h.1
  have hcomp : ∀ n x, (morV i rfl a h1).pull n ((resU (G q a) hle).hom.mapH n x) = (morV i rfl a h0).pull n x := by
    intro n x
    obtain ⟨z, hz, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
    rfl
  have hM : ∀ j, j ≠ a → Subsingleton ((CH.cx ((inU q V ⊓ On q i).ι ⋙ G q a)).H j) := by
    intro j hj
    have := hWsub j hj
    exact (hBij j).1.subsingleton
  have hga : Function.Surjective ((resU (G q a) hle).hom.mapH a) := by
    intro y
    obtain ⟨ω', hω'⟩ := he'b.2 ((morV i rfl a h1).pull a y)
    obtain ⟨ω, rfl⟩ := hFL.1 ω'
    refine ⟨e0 ω, (hBij a).1 ?_⟩
    rw [hcomp, hnat a e0 e' he0 he' ω]
    exact hω'
  have key : ∀ ι : Cx.Hom (RC (G q a) (inU q V) hQ) (CH.cx ((inU q V).ι ⋙ G q a)) (RingHom.id K),
      (∀ n x, ι.f n x = x.1) →
      (∀ j, j ≠ a → Subsingleton ((RC (G q a) (inU q V) hQ).H j)) ∧ Function.Injective (ι.mapH a) ∧
        ∀ x, x ∈ Set.range (ι.mapH a) ↔ (resU (G q a) hle).hom.mapH a x = 0 := by
    intro ι hι
    exact les_one ι (resU (G q a) hle).hom
      (fun n x y h => Subtype.ext (by rw [← hι, ← hι]; exact h))
      (fun n => res_exact (G q a) (inU q V) (On q i) hQ hle ι hι n)
      (fun n => res_surj (G q a) (inU q V) (On q i) hQ hle n) a hVsub hM hga
  let ι0 : Cx.Hom (RC (G q a) (inU q V) hQ) (CH.cx ((inU q V).ι ⋙ G q a)) (RingHom.id K) :=
    ⟨fun n => (relS ((inU q V).ι ⋙ G q a) (fun T => On q i T.obj) n).subtype, fun n x => rfl⟩
  refine ⟨(key ι0 fun _ _ => rfl).1, fun e he ι hι => ⟨(key ι hι).2.1, fun ω => ?_⟩⟩
  rw [(key ι hι).2.2, ← hker, ← hFL.2 ω]
  constructor
  · intro h
    apply he'b.1
    rw [← hnat a e e' he he' ω, ← hcomp, h, map_zero, map_zero]
  · intro h
    apply (hBij a).1
    rw [hcomp, hnat a e e' he he' ω, h, map_zero, map_zero]

end CrystallineSemistableComparison.Onto

end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.FormCup
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto.FormCupProduct

open CrystallineSemistableComparison.Onto Pb HT

theorem prod_mem_pdPow {b : Base} {L : b.Fun} (T : Thick L) : ∀ (n : ℕ) (f : Fin n → T.B), (∀ k, f k ∈ T.J) →
    ∏ k, f k ∈ T.pdPow n
  | 0, f, _ => by rw [Fin.prod_univ_zero, T.pdPow_zero]; trivial
  | n + 1, f, hf => by
    rw [Fin.prod_univ_succ, Pb.pdPow_eq]
    have := dividedPowerFiltration_mul T.δ 1 n (T.J_le_pdPow_one (hf 0)) (prod_mem_pdPow T n _ fun k => hf k.succ)
    rwa [Nat.add_comm] at this

variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem lift_sub_mem (Λ : Lifts q V) {T T' : (inU q V).FullSubcategory} (f : T ⟶ T') (g : Sec q V) :
    f.hom.φ (Λ.v T g) - Λ.v T' g ∈ T'.obj.J := by
  rw [← Ideal.Quotient.eq, Λ.hv T' g]
  have e : Ideal.Quotient.mk T'.obj.J (f.hom.φ (Λ.v T g)) =
      Ideal.quotientMap T'.obj.J f.hom.φ f.hom.hle (Ideal.Quotient.mk T.obj.J (Λ.v T g)) := rfl
  rw [e, Λ.hv T g]
  exact (GlobalTheory.CompanionTheory.GrForm.ev_nat f.hom T.property T'.property g).symm

theorem lift_mul_mem (Λ : Lifts q V) (T : (inU q V).FullSubcategory) (g h : Sec q V) :
    Λ.v T g * Λ.v T h - Λ.v T (g * h) ∈ T.obj.J := by
  rw [← Ideal.Quotient.eq, map_mul, Λ.hv, Λ.hv, Λ.hv]
  exact (map_mul _ g h).symm

theorem comp_φ {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) {i j k : Fin (n + 1)} (hij : i ≤ j)
    (hjk : j ≤ k) (y : (s.obj i).obj.B) :
    (s.map (homOfLE hjk)).hom.φ ((s.map (homOfLE hij)).hom.φ y) = (s.map (homOfLE (hij.trans hjk))).hom.φ y := by
  rw [show (homOfLE (hij.trans hjk) : i ⟶ k) = homOfLE hij ≫ homOfLE hjk from rfl, s.map_comp]
  rfl

def lv (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i : Fin (n + 1)) (x : Sec q V) :
    (s.obj (Fin.last n)).obj.B :=
  (s.map (homOfLE (Fin.le_last i))).hom.φ (Λ.v _ x)

theorem lv_sub_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i : Fin (n + 1))
    (x : Sec q V) : lv Λ s i x - Λ.v _ x ∈ (s.obj (Fin.last n)).obj.J :=
  lift_sub_mem Λ _ x

theorem lv_diff_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i j : Fin (n + 1))
    (x : Sec q V) : lv Λ s i x - lv Λ s j x ∈ (s.obj (Fin.last n)).obj.J := by
  have := sub_mem (lv_sub_mem Λ s i x) (lv_sub_mem Λ s j x)
  rwa [sub_sub_sub_cancel_right] at this

theorem lv_last (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x : Sec q V) :
    lv Λ s (Fin.last n) x = Λ.v _ x := by
  unfold lv
  rw [show (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ from rfl, s.map_id]
  rfl

theorem form_eq (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x₀ : Sec q V)
    (x : Fin n → Sec q V) :
    Λ.form x₀ x s = Λ.v _ x₀ * ∏ k : Fin n, (lv Λ s k.succ (x k) - lv Λ s k.castSucc (x k)) := rfl

theorem form_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x₀ : Sec q V)
    (x : Fin n → Sec q V) : Λ.form x₀ x s ∈ (s.obj (Fin.last n)).obj.pdPow n := by
  rw [form_eq]
  exact Ideal.mul_mem_left _ _ (prod_mem_pdPow _ n _ fun k => lv_diff_mem Λ s _ _ _)

theorem form_map (Λ : Lifts q V) {m n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n)
    (e : Fin (m + 1) → Fin (n + 1)) (he : Monotone e) (x₀ : Sec q V) (x : Fin m → Sec q V) :
    (s.map (homOfLE (Fin.le_last (e (Fin.last m))))).hom.φ (Λ.form x₀ x (he.functor ⋙ s)) =
      lv Λ s (e (Fin.last m)) x₀ * ∏ k : Fin m, (lv Λ s (e k.succ) (x k) - lv Λ s (e k.castSucc) (x k)) := by
  rw [Lifts.form, map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_sub]
  congr 1
  · exact comp_φ s (he (Fin.le_last k.succ)) (Fin.le_last _) _
  · exact comp_φ s (he (Fin.le_last k.castSucc)) (Fin.le_last _) _

theorem key (Λ : Lifts q V) {a a' : ℕ} (g₀ h₀ : Sec q V) (g : Fin a → Sec q V) (h : Fin a' → Sec q V)
    (s : ComposableArrows (inU q V).FullSubcategory (a + a')) :
    (s.map (homOfLE (Fin.le_last (CH.front (rfl : a + a' = a + a') (Fin.last a))))).hom.φ
        (Λ.form g₀ g ((CH.front_mono (rfl : a + a' = a + a')).functor ⋙ s)) *
      (s.map (homOfLE (Fin.le_last (CH.back (rfl : a + a' = a + a') (Fin.last a'))))).hom.φ
        (Λ.form h₀ h ((CH.back_mono (rfl : a + a' = a + a')).functor ⋙ s)) -
      Λ.form (g₀ * h₀) (Fin.append g h) s ∈ (s.obj (Fin.last (a + a'))).obj.pdPow (a + a' + 1) := by
  rw [form_map Λ s _ (CH.front_mono rfl), form_map Λ s _ (CH.back_mono rfl), form_eq Λ s, Fin.prod_univ_add]
  have e1 : ∀ k : Fin a, (Fin.castAdd a' k).succ = CH.front (rfl : a + a' = a + a') k.succ :=
    fun k => Fin.ext (by simp [CH.front])
  have e2 : ∀ k : Fin a, (Fin.castAdd a' k).castSucc = CH.front (rfl : a + a' = a + a') k.castSucc :=
    fun k => Fin.ext (by simp [CH.front])
  have e3 : ∀ k : Fin a', (Fin.natAdd a k).succ = CH.back (rfl : a + a' = a + a') k.succ :=
    fun k => Fin.ext (by simp [CH.back]; omega)
  have e4 : ∀ k : Fin a', (Fin.natAdd a k).castSucc = CH.back (rfl : a + a' = a + a') k.castSucc :=
    fun k => Fin.ext (by simp [CH.back])
  have e5 : CH.back (rfl : a + a' = a + a') (Fin.last a') = Fin.last (a + a') := Fin.ext (by simp [CH.back])
  simp only [Fin.append_left, Fin.append_right, e1, e2, e3, e4, e5, lv_last]
  have hF := prod_mem_pdPow (s.obj (Fin.last (a + a'))).obj a
    (fun k => lv Λ s (CH.front rfl k.succ) (g k) - lv Λ s (CH.front rfl k.castSucc) (g k))
    fun k => lv_diff_mem Λ s _ _ _
  have hB := prod_mem_pdPow (s.obj (Fin.last (a + a'))).obj a'
    (fun k => lv Λ s (CH.back rfl k.succ) (h k) - lv Λ s (CH.back rfl k.castSucc) (h k))
    fun k => lv_diff_mem Λ s _ _ _
  have hl : lv Λ s (CH.front rfl (Fin.last a)) g₀ * Λ.v _ h₀ - Λ.v _ (g₀ * h₀) ∈
      (s.obj (Fin.last (a + a'))).obj.J := by
    have := add_mem (Ideal.mul_mem_right (Λ.v _ h₀) _ (lv_sub_mem Λ s (CH.front rfl (Fin.last a)) g₀))
      (lift_mul_mem Λ _ g₀ h₀)
    convert this using 1
    ring
  have := dividedPowerFiltration_mul (s.obj (Fin.last (a + a'))).obj.δ 1 (a + a')
    ((s.obj (Fin.last (a + a'))).obj.J_le_pdPow_one hl) (dividedPowerFiltration_mul (s.obj (Fin.last (a + a'))).obj.δ a a' hF hB)
  rw [show 1 + (a + a') = a + a' + 1 by omega] at this
  rw [Pb.pdPow_eq]
  convert this using 1
  ring

end CrystallineSemistableComparison.Onto.FormCupProduct

namespace CrystallineSemistableComparison.Onto.FormCupProduct

open CrystallineSemistableComparison.Onto Pb HT

variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem term_eq (Λ : Lifts q V) {a n : ℕ}
    (f : CH.Cn (Pb.sq ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι) ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι)) a) (x₀ : Sec q V) (x : Fin a → Sec q V)
    (hf : ∀ s, (show sqM ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι)
      ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι) _ from f s).1 = Ideal.Quotient.mk _ (Λ.form x₀ x s))
    (s : ComposableArrows (inU q V).FullSubcategory n) (e : Fin (a + 1) → Fin (n + 1)) (he : Monotone e) :
    CH.term _ s f e he = sqMk (thFil (smFun Z q) (a : ℤ)) (thFil (smFun Z q) ((a : ℤ) + 1))
      ((s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom.φ (Λ.form x₀ x (he.functor ⋙ s)))
      ((thFil (smFun Z q) (a : ℤ)).map_mem (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom
        (form_mem Λ (he.functor ⋙ s) x₀ x)) := by
  apply Subtype.ext
  exact congrArg (Ideal.quotientMap ((thFil (smFun Z q) ((a : ℤ) + 1)).S (s.obj (Fin.last n)).obj)
    (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom.φ
    (fun z hz => (thFil (smFun Z q) ((a : ℤ) + 1)).map_mem (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom hz))
    (hf (he.functor ⋙ s))

end CrystallineSemistableComparison.Onto.FormCupProduct

namespace CrystallineSemistableComparison.Onto

open Pb HT FormCupProduct

theorem formCup_pf : FormCup := by
  intro K _ Z q V a a' g₀ h₀ g h x y hx hy Hx Hy
  let P : CH.Pairing ((inU q V).ι ⋙ G q a) ((inU q V).ι ⋙ G q a') ((inU q V).ι ⋙ G q (a + a')) :=
    ⟨fun T => (grOk (smFun Z q) (rfl : a + a' = a + a')).pair.μ T.obj, fun φ => (grOk (smFun Z q) rfl).pair.nat φ.hom⟩
  obtain ⟨hz, ez⟩ := CrystallineSemistableComparison.P.cup_cls P rfl x y hx hy
  refine ⟨hz, fun Λ => ?_⟩
  obtain ⟨f, hf, ef, hfs⟩ := Hx Λ
  obtain ⟨f', hf', ef', hfs'⟩ := Hy Λ
  obtain ⟨hz', ez'⟩ := CrystallineSemistableComparison.P.cup_cls P rfl f f' hf hf'
  refine ⟨P.cupC rfl f f', hz', ez.symm.trans ((congrArg₂ (P.cup rfl) ef ef').trans ez'), fun s => ?_⟩
  change ((grOk (smFun Z q) (rfl : a + a' = a + a')).mul (CH.term _ s f (CH.front rfl) (CH.front_mono rfl))
    (CH.term _ s f' (CH.back rfl) (CH.back_mono rfl))).1 = _
  rw [term_eq Λ f g₀ g hfs s _ (CH.front_mono rfl), term_eq Λ f' h₀ h hfs' s _ (CH.back_mono rfl), MulOk.mul_mk]
  exact Ideal.Quotient.eq.2 (key Λ g₀ h₀ g h s)

end CrystallineSemistableComparison.Onto
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.RelLiftOf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris
open GlobalTheory.CatH (face toLast)

universe w v u

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace RelativeFormLift

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

def liftS {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (s : ComposableArrows C n) (hs : Q (s.obj 0)) :
    ComposableArrows Q.FullSubcategory n :=
  Q.lift s fun k => hQ (s.map (homOfLE (Fin.zero_le _))) hs


open Classical in
def extZ {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (b : CH.Cn (Q.ι ⋙ F) n) : CH.Cn F n :=
  fun s => if hs : Q (s.obj 0) then b (liftS hQ s hs) else 0

theorem d_extZ {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (b : CH.Cn (Q.ι ⋙ F) n) (s : ComposableArrows C (n + 1))
    (hs : Q (s.obj 0)) : CH.d F n (extZ F hQ b) s = CH.d (Q.ι ⋙ F) n b (liftS hQ s hs) := by
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (extZ F hQ b (face i s)) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((Q.ι ⋙ F).map (toLast i (liftS hQ s hs))).hom (b (face i (liftS hQ s hs)))
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Q ((face i s).obj 0) := hQ (s.map (homOfLE (Fin.zero_le _))) hs
  have e : extZ F hQ b (face i s) = b (liftS hQ (face i s) h) := dif_pos h
  rw [e]
  rfl

end RelativeFormLift


open RelativeFormLift in
theorem relLiftOf_pf : RelLiftOf := by
  intro hS hO K _ W Z q i _ a n y hy
  have hQ : Cosieve (On q i) := (hS K W Z W q i i).2.1
  have hQ' : Cosieve ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i) :=
    fun _ _ f h => ⟨trivial, hQ f h.2⟩
  have h : ∀ T, (⊤ : ObjectProperty (Thick (smFun W (i ≫ q)))) T →
      ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i) ((smS i rfl).G.obj T) := fun T _ =>
    ⟨trivial, ((hS K W Z W q i i).2.2.2.2.2 T).1
      ⟨pullback.lift (pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T)
        (pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T) rfl,
        pullback.lift_snd _ _ _⟩⟩
  have hbij := hO K W Z q i ⊤ ⊤ h (fun _ _ => trivial) a n
  obtain ⟨⟨z₀, hz₀⟩, hy0⟩ := Submodule.Quotient.mk_surjective
    (((CH.cx (G q a)).B n).submoduleOf ((CH.cx (G q a)).Z n)) (show (CH.cx (G q a)).H n from y)
  have hz₀' : CH.d (G q a) n z₀ = 0 := hz₀
  subst hy0
  set w₀ := (CH.Mor.restrict (G q a) ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι).pullC n z₀ with hw
  have hw₀ : CH.d _ n w₀ = 0 := by rw [hw, CH.Mor.d_pullC, hz₀', map_zero]
  have e1 : (morV i rfl a h).pull n ((CH.cx _).cls w₀ hw₀) =
      (CH.Mor.restrict (G (i ≫ q) a) (⊤ : ObjectProperty (Thick (smFun W (i ≫ q)))).ι).pull n
        (pullH i rfl a n (Submodule.Quotient.mk ⟨z₀, hz₀⟩)) := rfl
  have e2 : (morV i rfl a h).pull n ((CH.cx _).cls w₀ hw₀) = 0 := by
    rw [e1, hy, map_zero]
  have e3 : (CH.cx _).cls w₀ hw₀ = 0 := hbij.1 (by rw [e2, map_zero])
  have e4 : w₀ ∈ (CH.cx (((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι ⋙ G q a)).B n :=
    (Submodule.Quotient.mk_eq_zero (((CH.cx _).B n).submoduleOf ((CH.cx _).Z n))
      (x := (⟨w₀, hw₀⟩ : (CH.cx (((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι ⋙ G q a)).Z n))).1 e3
  cases n with
  | zero =>
    have e5 : w₀ = 0 := (Submodule.mem_bot K).1 e4
    refine ⟨z₀, hz₀', fun s hs => ?_, rfl⟩
    exact congrFun e5 (liftS hQ' s ⟨trivial, hs⟩)
  | succ m =>
    obtain ⟨b', hb'⟩ := e4
    have hz : CH.d (G q a) (m + 1) (z₀ - CH.d (G q a) m (extZ (G q a) hQ' b')) = 0 := by
      rw [map_sub, hz₀', CH.d_d, sub_zero]
    refine ⟨z₀ - CH.d (G q a) m (extZ (G q a) hQ' b'), hz, fun s hs => ?_, ?_⟩
    · change z₀ s - CH.d (G q a) m (extZ (G q a) hQ' b') s = 0
      rw [d_extZ (G q a) hQ' b' s ⟨trivial, hs⟩]
      rw [hb']
      exact sub_self _
    · show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      rw [Submodule.Quotient.eq]
      refine ⟨-extZ (G q a) hQ' b', ?_⟩
      rw [map_neg]
      change -(CH.d (G q a) m (extZ (G q a) hQ' b')) = (z₀ - CH.d (G q a) m (extZ (G q a) hQ' b')) - z₀
      abel

end CrystallineSemistableComparison.Onto

end
end

