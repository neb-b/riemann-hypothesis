module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def Hyps : Prop :=
  A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧ B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ B7 ∧ C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧
    D1 ∧ D2 ∧ D3 ∧ E1 ∧ E2 ∧ E3

abbrev Sp (A : Type) [CommRing A] : Scheme.{0} := Spec (CommRingCat.of A)

abbrev pl (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X) (m : ℤ) : Ht q (sch.obj X) m i →+ Ht q (sch.obj Y) m i :=
  pull (ZMod q) (sch.map f) (tw q i) m

def IsCurve {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) : Prop :=
  IsIntegral C ∧ IsProper c ∧ SmoothOfRelativeDimension 1 c

def SmP {Y B : Scheme.{0}} (p : Y ⟶ B) (V : B.Opens) : Prop := IsProper p ∧ Smooth (p ∣_ V)

abbrev fibMap {Y1 Y0 B S : Scheme.{0}} (g : Y1 ⟶ Y0) (p : Y0 ⟶ B) (s : S ⟶ B) : pullback (g ≫ p) s ⟶ pullback p s :=
  pullback.map (g ≫ p) s p s g (𝟙 _) (𝟙 _) (by simp) (by simp)

def H0TwistOverClosedField : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) → ∀ i : ℤ,
  Finite (Ht q (sp Ω) 0 i) ∧ ∀ {X : Scheme.{0}} [ConnectedSpace X] (c : X ⟶ Sp Ω), Function.Bijective (pl q i c 0)

def LeafPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p], topologicalKrullDim X ≤ 0 → ∀ n i : ℤ,
  Finite (Ht q (sch.obj X) n i)

def LeafComp : Prop := Hyps → ∀ (q : ℕ) (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (n i : ℤ),
  (∀ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι → IsIntegral Z → Finite (Ht q (sch.obj Z) n i)) →
  ∃ (Y : Scheme.{0}) (f : Y ⟶ X), IsProper f ∧ Surjective f ∧ Finite (Ht q (sch.obj Y) n i)

def LeafDesc : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) →
  ∀ {Y X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (f : Y ⟶ X) [IsProper f] [Surjective f] (i : ℤ), Eqv _ (cechAug f) (tw q i)

def LeafSS : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] (n : ℤ),
  Eqv R (cechAug f) F → (∀ (Z : Scheme.{0}) (g : Z ⟶ X), IsProper g → ∀ m < n, Finite (H R (sch.obj Z) F m)) →
  Finite (pull R (sch.map f) F n).ker

def LeafUnits : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], Finite (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range)

def LeafPic : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → Finite {c : CommRing.Pic B // c ^ q = 1}

def LeafKum : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B],
  IsUnit (q : k) → Finite (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) → Finite {c : CommRing.Pic B // c ^ q = 1} →
  ∀ i : ℤ, Finite (Ht q (sp B) 1 i)

def LeafCurve : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) → ∀ i : ℤ,
  (∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B], Finite (Ht q (sp B) 1 i)) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → Finite (Ht q (sch.obj C) 1 i) ∧ Finite (Ht q (sch.obj C) 2 i) ∧
    ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj C) m i)

def LeafKill : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → Finite (Ht q (sch.obj C) m i) →
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m = 0

def Family {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0)
    (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B W Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (ι : W ⟶ B) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ IsClosedImmersion ι ∧ (V : Set B) = (Set.range ι)ᶜ ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧ Surjective (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    topologicalKrullDim (pullback p ι : Scheme.{0}) < topologicalKrullDim X ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2

def LeafGeo : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 ∧ ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) →
      IsCurve (γ2 ≫ γ1 ≫ c0) → Surjective γ1 → Surjective γ2 → Family (k := k) X c0 γ1 γ2

def LeafSpec : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B Y0 Y1 : Scheme.{0}} [IsIntegral B] (_ : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g : Y1 ⟶ Y0), SmP p V → SmP (g ≫ p) V →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ B), Set.range s ⊆ V →
  ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ : C1 ⟶ C0) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1),
    IsPullback u0 c0 p s → IsPullback u1 (γ ≫ c0) (g ≫ p) s → γ ≫ u0 = u1 ≫ g →
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, Subsingleton (Ht q (sch.obj C0) m i) → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧
    (∀ m, pl q i γ m = 0 → pl q i (fibMap g p t) m = 0) ∧
    (Function.Bijective (pl q i (γ ≫ c0) 0) → Function.Bijective (pl q i (pullback.snd (g ≫ p) t) 0))

def LeafGhost : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (n : ℤ) (a : Ht q (sch.obj Y0) n i), pl q i (pullback.fst p ι) n a = 0 →
    ∃ b : Ht q (sch.obj B) n i, pl q i (g2 ≫ g1 ≫ p) n b = pl q i (g2 ≫ g1) n a

theorem fin_of {A C D E : Type*} [AddCommGroup A] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] (φ : A →+ C)
    (r : A →+ D) (ψ : E →+ C) [Finite D] [Finite E] (hk : Finite φ.ker) (h : ∀ a, r a = 0 → ∃ b, ψ b = φ a) : Finite A := by
  rw [AddMonoidHom.finite_iff_finite_ker_range r]
  refine ⟨?_, inferInstance⟩
  rw [AddMonoidHom.finite_iff_finite_ker_range (φ.comp r.ker.subtype)]
  constructor
  · exact Finite.of_injective (fun x : (φ.comp r.ker.subtype).ker => (⟨x.1.1, x.2⟩ : φ.ker))
      (fun x y hxy => Subtype.ext (Subtype.ext (congrArg (fun z : φ.ker => z.1) hxy)))
  · have : (Set.range ψ).Finite := Set.finite_range _
    refine Set.Finite.subset this ?_
    rintro _ ⟨a, rfl⟩
    exact h a.1 a.2

theorem pl_comp (q : ℕ) (i : ℤ) {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (m : ℤ) (x : Ht q (sch.obj X) m i) :
    pl q i (g ≫ f) m x = pl q i g m (pl q i f m x) := by
  rw [← pull_comp, ← Functor.map_comp]

theorem goal_of (hH0 : H0TwistOverClosedField) (hPt : LeafPt) (hComp : LeafComp) (hDesc : LeafDesc) (hSS : LeafSS) (hU : LeafUnits)
    (hPic : LeafPic) (hKum : LeafKum) (hCurve : LeafCurve) (hKill : LeafKill) (hGeo : LeafGeo) (hSpec : LeafSpec)
    (hGhost : LeafGhost) : LateralTheory.E.EtaleChapterEFour := by
  intro a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 b1 b2 b3 b4 b5 b7 c1 c2 c3 c4 c5 d1 d2 d3 e1 e2 e3
  have hy : Hyps := ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7, c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3⟩
  intro q _ k _ _ hq X p _ n i
  have step : ∀ n : ℤ, (∀ (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → ∀ m < n, Finite (Ht q (sch.obj X) m i)) →
      ∀ (e : WithBot ℕ∞) (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → topologicalKrullDim X ≤ e →
        Finite (Ht q (sch.obj X) n i) := by
    intro n Q
    have ker : ∀ (X Y : Scheme.{0}) (p : X ⟶ Sp k) (f : Y ⟶ X), IsProper p → IsProper f → Surjective f →
        Finite (pl q i f n).ker := fun X Y p f _ _ _ =>
      hSS hy _ _ f n (hDesc hy q k hq p f i) (fun Z g _ => Q Z (g ≫ p) inferInstance)
    intro e
    induction e using WellFoundedLT.induction with
    | ind e IH =>
    have int : ∀ (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → IsIntegral X → topologicalKrullDim X ≤ e →
        Finite (Ht q (sch.obj X) n i) := by
      intro X p _ _ he
      rcases le_or_gt (topologicalKrullDim X) 0 with h0 | h0
      · exact hPt hy q k hq p h0 n i
      obtain ⟨Ω, _, _, _, C0, c0, hc0, hall⟩ := hGeo k p h0
      have hΩ : IsUnit (q : Ω) := by simpa using hq.map (algebraMap k Ω)
      have hc : ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → _ := fun c => hCurve hy q Ω hΩ i
        (fun B _ _ _ _ => hKum hy q Ω B hΩ (hU q Ω B) (hPic hy q Ω B hΩ) i) c
      obtain ⟨C1, γ1, hc1, s1, z1⟩ := hKill hy q Ω hΩ c0 hc0 2 i (by norm_num) (hc c0 hc0).2.1
      obtain ⟨C2, γ2, hc2, s2, z2⟩ := hKill hy q Ω hΩ (γ1 ≫ c0) hc1 1 i (by norm_num) (hc _ hc1).1
      obtain ⟨B, W, Y0, Y1, Y2, b, ι, V, π, g1, g2, h, s, u0, u1, u2, _, _, _, hV, hs, m0, m1, m2, f1, f2, dB, dW,
        P0, P1, P2, w1, w2⟩ := hall C1 C2 γ1 γ2 hc1 hc2 s1 s2
      have := m0.1
      have := hc2.1
      have fB := IH _ (dB.trans_le he) B b inferInstance le_rfl
      have fW := IH _ (dW.trans_le he) (pullback π ι) (pullback.fst π ι ≫ π ≫ b) inferInstance le_rfl
      have G := hGhost hy q k hq i b ι V hV π g1 g2 m0.1 m1.1 m2.1 (fun A _ t hA ht => by
        have S1 := hSpec hy q k hq i b V π g1 m0 m1 Ω s hs c0 γ1 u0 u1 P0 P1 w1 A t hA ht
        have S2 := hSpec hy q k hq i b V (g1 ≫ π) g2 m1 m2 Ω s hs (γ1 ≫ c0) γ2 u1 u2 P1 P2 w2 A t hA ht
        exact ⟨fun m hm => S1.1 m ((hc c0 hc0).2.2 m hm), S1.2.1 2 z1, S2.2.1 1 z2,
          S2.2.2 ((hH0 hy q Ω hΩ i).2 _)⟩) n
      refine fin_of (pl q i (g2 ≫ g1 ≫ h) n) (pl q i (pullback.fst π ι ≫ h) n) (pl q i (g2 ≫ g1 ≫ π) n)
        (ker X Y2 p _ inferInstance f1 f2) (fun a ha => ?_)
      rw [pl_comp] at ha
      obtain ⟨x, hx⟩ := G _ ha
      exact ⟨x, by rw [hx, ← pl_comp, Category.assoc]⟩
    intro X p _ he
    obtain ⟨Y, f, f1, f2, f3⟩ := hComp hy q k p n i (fun Z ι _ _ =>
      int Z (ι ≫ p) inferInstance inferInstance (ι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans he))
    have := ker X Y p f inferInstance f1 f2
    rw [AddMonoidHom.finite_iff_finite_ker_range (pl q i f n)]
    exact ⟨this, inferInstance⟩
  have all : ∀ (N : ℕ) (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → ∀ m < (N : ℤ), Finite (Ht q (sch.obj X) m i) := by
    intro N
    induction N with
    | zero =>
      intro X p _ m hm
      have := (a9 (ZMod q) (tw q i)).1 (sch.obj X) m (by simpa using hm)
      exact Finite.of_subsingleton
    | succ N IH =>
      intro X p hp m hm
      rcases lt_or_eq_of_le (show m ≤ N by omega) with h | h
      · exact IH X p hp m h
      · subst h
        exact step _ IH _ X p hp le_rfl
  exact all (n.toNat + 1) X p inferInstance n (by omega)

end LateralTheory.E.E4

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCGoodPf
section
open LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LCGoodPf

theorem closed_empty {C : Type} [CommRing C] {J : Ideal C} (hJ : J ≤ Ideal.jacobson ⊥)
    (Z : Set (PrimeSpectrum C)) (hZ : IsClosed Z)
    (h : ∀ z : PrimeSpectrum (C ⧸ J), PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∉ Z) : Z = ∅ := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  by_cases hI : I = ⊤
  · subst hI; simp
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  exfalso
  have hJM : J ≤ M := le_trans hJ (sInf_le ⟨bot_le, hM⟩)
  have hp : (⟨M, hM.isPrime⟩ : PrimeSpectrum C) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ M := by rw [Ideal.mk_ker]; exact hJM
    have := hM.isPrime
    have hpr : (M.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    refine ⟨⟨M.map (Ideal.Quotient.mk J), hpr⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.map _ M) = M
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_eq_left.2 ?_
    rw [← RingHom.ker_eq_comap_bot]; exact hker
  obtain ⟨z, hz⟩ := hp
  apply h z
  rw [hz]
  exact hIM

theorem lcMap_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Y : Type}
    (φ : LocallyConstant (PrimeSpectrum A) Y) (z : PrimeSpectrum B) :
    lcMap f φ z = φ (PrimeSpectrum.comap f z) := rfl

theorem isClosed_ne {X Y : Type} [TopologicalSpace X] (a b : LocallyConstant X Y) :
    IsClosed {x | a x ≠ b x} := by
  have : IsLocallyConstant (fun x => (a x = b x : Prop)) :=
    IsLocallyConstant.comp₂ a.isLocallyConstant b.isLocallyConstant (fun u v => (u = v : Prop))
  have h2 := this.isClosed_fiber False
  convert h2 using 1
  ext x; simp

theorem LCGood_of : LCGood := by
  intro C _ J hG Y
  obtain ⟨hJ, hlift⟩ := hG
  constructor
  · intro a b hab
    have hZ := closed_empty hJ _ (isClosed_ne a b) (fun z hz => hz (by
      have := congrArg (fun φ => φ z) hab
      simpa [lcMap_apply] using this))
    ext x
    by_contra hx
    have : x ∈ ({x | a x ≠ b x} : Set _) := hx
    rw [hZ] at this; exact this
  · intro ψ

    have hU : ∀ y : Y, ∃ U : Set (PrimeSpectrum C), IsClopen U ∧
        PrimeSpectrum.comap (Ideal.Quotient.mk J) ⁻¹' U = ψ ⁻¹' {y} := by
      intro y
      obtain ⟨e, he, hF⟩ := PrimeSpectrum.isClopen_iff.1 (ψ.isLocallyConstant.isClopen_fiber y)
      obtain ⟨x, hx, hxe⟩ := hlift e he
      refine ⟨PrimeSpectrum.basicOpen x, PrimeSpectrum.isClopen_iff.2 ⟨x, hx, rfl⟩, ?_⟩
      have hF' : ψ ⁻¹' {y} = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (C ⧸ J))) := hF
      rw [hF', ← hxe]
      ext p
      simp
    choose U hUc hUp using hU
    have hmem : ∀ z y, PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∈ U y ↔ ψ z = y := by
      intro z y
      have := congrArg (fun s => z ∈ s) (hUp y)
      simpa using this
    have hcover : ∀ x, ∃ y, x ∈ U y := by
      have hE := closed_empty hJ (⋃ y, U y)ᶜ
        (isOpen_iUnion (fun y => (hUc y).isOpen)).isClosed_compl
        (fun z hz => hz (Set.mem_iUnion.2 ⟨ψ z, (hmem z _).2 rfl⟩))
      intro x
      by_contra hx
      push Not at hx
      have : x ∈ (⋃ y, U y)ᶜ := by simpa using hx
      rw [hE] at this
      exact this
    have huniq : ∀ x y y', x ∈ U y → x ∈ U y' → y = y' := by
      intro x y y' h1 h2
      by_contra hne
      have := closed_empty hJ (U y ∩ U y') ((hUc y).isClosed.inter (hUc y').isClosed)
        (fun z hz => hne (((hmem z y).1 hz.1).symm.trans ((hmem z y').1 hz.2)))
      have hx : x ∈ U y ∩ U y' := ⟨h1, h2⟩
      rw [this] at hx; exact hx
    classical
    let g : PrimeSpectrum C → Y := fun x => Classical.choose (hcover x)
    have hg : ∀ x y, g x = y ↔ x ∈ U y := by
      intro x y
      constructor
      · rintro rfl; exact Classical.choose_spec (hcover x)
      · intro h; exact huniq x _ _ (Classical.choose_spec (hcover x)) h
    have hgl : IsLocallyConstant g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro y
      have : g ⁻¹' {y} = U y := by ext x; simp [hg]
      rw [this]; exact (hUc y).isOpen
    refine ⟨⟨g, hgl⟩, ?_⟩
    ext z
    rw [lcMap_apply]
    exact (hg _ _).2 ((hmem z _).2 rfl)

end LateralTheory.E.LCGoodPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCSplitPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LCSplitPf
open LateralTheory.E.t_E1Cut

def Idem : Prop := ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R] (φ : LocallyConstant (PrimeSpectrum R) (ZMod q)),
  ∃ ε : ZMod q → R, CompleteOrthogonalIdempotents ε ∧ ∀ (p : PrimeSpectrum R) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal

def Torsor : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q)) (ε : ZMod q → Localization.Away (f * g)),
  CompleteOrthogonalIdempotents ε → (∀ (p : PrimeSpectrum (Localization.Away (f * g))) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal) →
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra S C), Algebra.Etale S C ∧ Module.Finite S C ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) ∧
    (Nonempty (C →ₐ[S] S) → ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b)

theorem LCSplit_of_idem (hF : FinEtSection) (hI : Idem) (hT : Torsor) : LCSplit := by
  intro q _ S _ hS f g hfg φ
  obtain ⟨ε, hε, hφ⟩ := hI q _ φ
  obtain ⟨C, _, _, hEt, hFin, hSurj, hsec⟩ := hT q S f g hfg φ ε hε hφ
  exact hsec (hF S C hS hSurj)

theorem idem_of : Idem := by
  intro q _ R _ φ
  classical
  let E := fun c : ZMod q => PrimeSpectrum.isIdempotentElemEquivClopens (R := R) |>.symm
    ⟨{x | φ x = c}, φ.isLocallyConstant.isClopen_fiber c⟩
  have hB : ∀ c, PrimeSpectrum.basicOpen (E c).1 = ⟨{x | φ x = c}, (φ.isLocallyConstant.isClopen_fiber c).isOpen⟩ :=
    fun c => PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _
  have hmem : ∀ (p : PrimeSpectrum R) c, φ p = c ↔ (E c).1 ∉ p.asIdeal := by
    intro p c
    have := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) => p ∈ U) (hB c)
    simp only [PrimeSpectrum.mem_basicOpen] at this
    exact (this.to_iff.trans (by rfl)).symm
  refine ⟨fun c => (E c).1, ?_, hmem⟩
  have hid : ∀ c, IsIdempotentElem (E c).1 := fun c => (E c).2
  have horth : OrthogonalIdempotents (fun c => (E c).1) := by
    refine ⟨hid, ?_⟩
    intro c d hcd
    apply IsIdempotentElem.eq_zero_of_isNilpotent ((hid c).mul (hid d))
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    by_contra h
    have hc : (E c).1 ∉ J := fun hc => h (J.mul_mem_right _ hc)
    have hd : (E d).1 ∉ J := fun hd => h (J.mul_mem_left _ hd)
    exact hcd (((hmem ⟨J, hJ⟩ c).2 hc).symm.trans ((hmem ⟨J, hJ⟩ d).2 hd))
  refine CompleteOrthogonalIdempotents.of_prod_one_sub horth ?_
  have hP : IsIdempotentElem (∏ c, (1 - (E c).1)) := by
    classical
    induction (Finset.univ : Finset (ZMod q)) using Finset.induction_on with
    | empty => simpa using IsIdempotentElem.one
    | insert a s ha ih => rw [Finset.prod_insert ha]; exact (hid a).one_sub.mul ih
  apply IsIdempotentElem.eq_zero_of_isNilpotent hP
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  rw [Ideal.IsPrime.prod_mem_iff]
  refine ⟨φ ⟨J, hJ⟩, Finset.mem_univ _, ?_⟩
  have hn : (E (φ ⟨J, hJ⟩)).1 ∉ J := (hmem ⟨J, hJ⟩ _).1 rfl
  have h0 : (E (φ ⟨J, hJ⟩)).1 * (1 - (E (φ ⟨J, hJ⟩)).1) ∈ J := by
    rw [mul_sub, mul_one, (hid _).eq, sub_self]; exact J.zero_mem
  exact (hJ.mem_or_mem h0).resolve_left hn

theorem LCSplit_of (hF : FinEtSection) (hT : Torsor) : LCSplit := LCSplit_of_idem hF idem_of hT

section Conc
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

def twist (hε : CompleteOrthogonalIdempotents ε) : (ZMod q → A) →+* (ZMod q → A) where
  toFun z k := ∑ c, ε c * z (k + c)
  map_one' := by funext k; simp [hε.complete]
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_mul' x y := by
    funext k
    simp only [Pi.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [show ε c * x (k + c) * (ε c * y (k + c)) = (ε c * ε c) * (x (k + c) * y (k + c)) by ring, (hε.idem c).eq]
    · intro d _ hdc
      rw [show ε c * x (k + c) * (ε d * y (k + d)) = (ε c * ε d) * (x (k + c) * y (k + d)) by ring, hε.ortho (Ne.symm hdc), zero_mul]
    · simp
end Conc

section Tor
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}

abbrev Amb (q : ℕ) := (ZMod q → Localization.Away f) × (ZMod q → Localization.Away g)

def h1 : Amb f g q →+* (ZMod q → Localization.Away (f * g)) :=
  Pi.ringHom fun k => (rL f g).comp ((Pi.evalRingHom _ k).comp (RingHom.fst _ _))

def h2 (hε : CompleteOrthogonalIdempotents ε) : Amb f g q →+* (ZMod q → Localization.Away (f * g)) :=
  (twist hε).comp (Pi.ringHom fun k => (rR f g).comp ((Pi.evalRingHom _ k).comp (RingHom.snd _ _)))

def Tor (hε : CompleteOrthogonalIdempotents ε) : Subring (Amb f g q) := RingHom.eqLocus (h1 f g) (h2 f g hε)

def torMap (hε : CompleteOrthogonalIdempotents ε) : S →+* Tor f g hε :=
  RingHom.codRestrict (RingHom.prod ((Pi.constRingHom (ZMod q) _).comp (algebraMap S _))
    ((Pi.constRingHom (ZMod q) _).comp (algebraMap S _))) (Tor f g hε) (by
    intro s
    show h1 f g _ = h2 f g hε _
    funext k
    change rL f g (algebraMap S _ s) = ∑ c, ε c * rR f g (algebraMap S _ s)
    unfold rL rR
    rw [IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq, ← Finset.sum_mul, hε.complete, one_mul])
end Tor

def TorEt : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Algebra.Etale S (Tor f g hε) ∧ Module.Finite S (Tor f g hε) ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap S (Tor f g hε)))

def TorSec : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q)) (ε : ZMod q → Localization.Away (f * g))
  (hε : CompleteOrthogonalIdempotents ε), (∀ (p : PrimeSpectrum (Localization.Away (f * g))) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal) →
  letI := (torMap f g hε).toAlgebra
  Nonempty (Tor f g hε →ₐ[S] S) → ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b

theorem torsor_of (hE : TorEt) (hS : TorSec) : Torsor := by
  intro q _ S _ f g hfg φ ε hε hφ
  letI := (torMap f g hε).toAlgebra
  obtain ⟨h1, h2, h3⟩ := hE q S f g hfg ε hε
  exact ⟨Tor f g hε, inferInstance, (torMap f g hε).toAlgebra, h1, h2, h3, hS q S f g hfg φ ε hε hφ⟩

theorem LCSplit_of_tor (hF : FinEtSection) (hE : TorEt) (hS : TorSec) : LCSplit := LCSplit_of hF (torsor_of hE hS)

end LateralTheory.E.LCSplitPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNatOnePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatOnePf

variable {R : Type} [CommRing R]

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp] at h
  unfold freeGen
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y) ?_)
  exact ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (g.app (op U))) (ULift.up.{1} x)

theorem chainsXIso_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  unfold chainsXIso chains
  rw [Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by omega) (by omega), Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_nat, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem LeafNatOne_of (hOne : LateralTheory.E.CupProductRingLaws.LeafOneSpec) : LateralTheory.E.CupProductRingLaws.LeafNatOne := by
  intro q _ E E' f hE'
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨(f.app (op (SimplexCategory.mk 0))).app (op U) x⟩
  obtain ⟨⟨α, hα⟩, h'⟩ := hOne q E' hE'
  rw [h' α hα]
  let β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0 :=
    zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) α (zero_add 0)
  have hβ : LateralTheory.E.CupProductRingLaws.IsOneCocycle q E β := fun U x ζ => by
    rw [← hα U ((f.app (op (SimplexCategory.mk 0))).app (op U) x) ζ]
    exact ev_pull f α.1 0 0 _ U x
  rw [(hOne q E hE).2 β hβ]
  rfl

end LateralTheory.E.LeafNatOnePf
end
end

