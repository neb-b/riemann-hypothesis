module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignCancel
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.Staircase

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem term_ιC {F : C ⥤ ModuleCat.{0} R} (T : Res.{1} F) (hT : T.Good) {p n : ℕ}
    (s : ComposableArrows C n) (z : Cn F p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K 0) s (T.ιC p z) g hg = T.ι _ (term F s z g hg) :=
  (hT.ι_nat _ _).symm

theorem term_dvC {F : C ⥤ ModuleCat.{0} R} (T : Res.{1} F) (hT : T.Good) (t : ℕ) {p n : ℕ}
    (s : ComposableArrows C n) (a : Cn (T.K t) p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K (t + 1)) s (T.dvC t p a) g hg = T.dv t _ (term (T.K t) s a g hg) :=
  (hT.dv_nat t _ _).symm

theorem sign_cancel {i k r : ℕ} (h : i + k = r) : (-1 : ℤ) ^ r * (-1 : ℤ) ^ i = (-1 : ℤ) ^ k := by
  subst h
  rw [pow_add, mul_comm ((-1 : ℤ) ^ i), mul_assoc, ← mul_pow]
  simp

theorem stCupB : CupLeib.{1} → StCol → StCupB := by
  intro hL hC R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ g₁ g₂ i j n hn z z' hz t
  induction t with
  | zero =>
    intro k r h y hy
    obtain ⟨rfl, rfl⟩ := hy
    subst h
    subst hn
    refine ⟨rfl, ?_⟩
    funext s
    change T₃.ι _ (P.μ _ (term F₁ s z _ _) (term F₂ s z' _ _)) =
      (μ.μ 0 0 0 (zero_add 0)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K 0) s (T₂.ιC _ z') _ _)
    rw [term_ιC T₁ g₁, term_ιC T₂ g₂]
    exact (μ.ι _ _ _).symm
  | succ t ih =>
    intro k r h y hy
    obtain ⟨a, rfl, ha⟩ := hy
    have hd : d (T₁.K 0) i (T₁.ιC i z) = 0 := by
      rw [(hC R C F₁ T₁ g₁).1, hz, map_zero]
    refine ⟨(μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a, ?_, ?_⟩
    · funext s
      change T₃.dv t _ ((μ.μ 0 t t (zero_add t)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K t) s a _ _)) =
        (μ.μ 0 (t + 1) (t + 1) (zero_add (t + 1))).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _)
          (term (T₂.K (t + 1)) s (T₂.dvC t k a) _ _)
      rw [μ.leib 0 t t (zero_add t), term_dvC T₂ g₂, term_ιC T₁ g₁,
        (g₁.ex0 _ _).mpr ⟨_, rfl⟩, map_zero, LinearMap.zero_apply, zero_add, pow_zero, one_smul]
    · have e := hL R C (T₁.K 0) (T₂.K t) (T₃.K t) (μ.μ 0 t t (zero_add t)) i k r h (T₁.ιC i z) a
      have key := ih (k + 1) (r + 1) (by omega) ((-1 : ℤ) ^ k • d (T₂.K t) k a) ha
      have e' : (-1 : ℤ) ^ r • d (T₃.K t) r ((μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a) =
          (μ.μ 0 t t (zero_add t)).cupC (show i + (k + 1) = r + 1 by omega) (T₁.ιC i z)
            ((-1 : ℤ) ^ k • d (T₂.K t) k a) := by
        rw [e, hd, map_zero, LinearMap.zero_apply, zero_add, smul_smul, sign_cancel h, map_zsmul]
      rw [e']
      exact key

end GlobalTheory.CompanionTheory.Staircase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCol
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stCol : CrystallineSemistableComparison.E.StCol := by
  intro R _ C _ F T hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k z
    funext s
    change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K 0).map (GlobalTheory.CatH.toLast i s)).hom (T.ι _ (z (GlobalTheory.CatH.face i s))) =
      T.ι _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        (F.map (GlobalTheory.CatH.toLast i s)).hom (z (GlobalTheory.CatH.face i s)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hG.ι_nat]
  · intro s k a
    funext t
    change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K (s + 1)).map (GlobalTheory.CatH.toLast i t)).hom (T.dv s _ (a (GlobalTheory.CatH.face i t))) =
      T.dv s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K s).map (GlobalTheory.CatH.toLast i t)).hom (a (GlobalTheory.CatH.face i t)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hG.dv_nat]
  · intro k x y h
    funext s
    exact hG.inj _ (congrFun h s)
  · intro k x
    constructor
    · intro h
      have hz : ∀ s, ∃ z, T.ι _ z = x s := fun s => (hG.ex0 _ (x s)).1 (congrFun h s)
      choose z hz using hz
      exact ⟨z, funext hz⟩
    · rintro ⟨z, rfl⟩
      funext s
      exact (hG.ex0 _ _).2 ⟨_, rfl⟩
  · intro s k x
    constructor
    · intro h
      have hz : ∀ t, ∃ a, T.dv s _ a = x t := fun t => (hG.ex s _ (x t)).1 (congrFun h t)
      choose a ha using hz
      exact ⟨a, funext ha⟩
    · rintro ⟨a, rfl⟩
      funext t
      exact (hG.ex s _ _).2 ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.EdgeStair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StExOfStCol
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stEx_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StEx := by
  intro hcol R _ C _ F T hG s
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hG
  induction s with
  | zero =>
    intro k j hsk x hv hd
    have hjk : j = k := by omega
    subst hjk
    obtain ⟨z, hz⟩ := (hex0 j x).1 hv
    refine ⟨z, ?_, ⟨rfl, hz⟩⟩
    apply hinj (j + 1)
    rw [← hι, hz, hd, map_zero]
  | succ s ih =>
    intro k j hsk x hv hd
    obtain ⟨a, ha⟩ := (hex s k x).1 hv
    have h1 : T.dvC s (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, ← hdv, ha, hd, smul_zero]
    have h2 : d (T.K s) (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, d_d, smul_zero]
    obtain ⟨z, hz, hst⟩ := ih (k + 1) j (by omega) _ h1 h2
    exact ⟨z, hz, ⟨a, ha, hst⟩⟩

end GlobalTheory.CompanionTheory.EdgeStair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StTopOfStCol
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem stTop_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StTop := by
  intro hCol R _ C _ F T hT j z hz s
  obtain ⟨hι, hdv, -, hex0, hex⟩ := hCol R C F T hT
  induction s with
  | zero =>
    intro k x hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨(hex0 j _).2 ⟨_, rfl⟩, by rw [hι, hz, map_zero]⟩
  | succ s ih =>
    intro k x hx
    obtain ⟨a, rfl, ha⟩ := hx
    have h1 := (ih (k + 1) _ ha).1
    rw [map_zsmul] at h1
    have h2 : T.dvC s (k + 1) (d _ k a) = 0 :=
      (IsUnit.smul_eq_zero ((isUnit_neg_one (α := ℤ)).pow k)).1 h1
    exact ⟨(hex s k _).2 ⟨a, rfl⟩, by rw [hdv]; exact h2⟩

end GlobalTheory.CompanionTheory.EdgeMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StUniq
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stUniq : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StUniq := by
  intro hcol R _ C _ F T hT j z
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hT
  have key : ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T.BZ s k x → z ∈ (cx F).B j := by
    intro s
    induction s with
    | zero =>
      intro k x hS hB
      obtain ⟨h, rfl⟩ := hS
      subst h
      cases j with
      | zero =>
        have h0 : T.ιC 0 z = 0 := hB
        have hz : z = 0 := hinj 0 (by rw [h0, map_zero])
        rw [hz]
        exact Submodule.zero_mem _
      | succ k =>
        obtain ⟨b, hb, hdb⟩ := hB
        obtain ⟨z', rfl⟩ := (hex0 k b).1 hb
        refine (⟨z', ?_⟩ : z ∈ LinearMap.range (d F k))
        apply hinj (k + 1)
        rw [← hι]
        exact hdb
    | succ s ih =>
      intro k x hS hB
      obtain ⟨a, rfl, hS'⟩ := hS
      cases k with
      | zero =>
        exact ih 1 _ hS' ⟨a, hB, by simp⟩
      | succ k =>
        obtain ⟨b, hb, hdb⟩ := hB
        obtain ⟨b', rfl⟩ := (hex s k b).1 hb
        refine ih (k + 2) _ hS' ⟨(-1 : ℤ) ^ (k + 1) • (a - d _ k b'), ?_, ?_⟩
        · rw [map_zsmul, map_sub, ← hdv, hdb, sub_self, smul_zero]
        · rw [map_zsmul, map_sub, d_d, sub_zero]
  intro s k x hS hB
  exact key s k x hS hB

end GlobalTheory.CompanionTheory.EdgeStair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StairCupFirst
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairCupFirst

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}
  {T₁ : Res.{1} F₁} {T₂ : Res.{1} F₂} {T₃ : Res.{1} F₃} {P : Pairing F₁ F₂ F₃}

theorem term_dvC {F : C ⥤ ModuleCat.{0} R} {T : Res.{1} F} (hT : T.Good) {s p n : ℕ}
    (σ : ComposableArrows C n) (a : Cn (T.K s) p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K (s + 1)) σ (T.dvC s p a) g hg = T.dv s _ (term (T.K s) σ a g hg) := by
  delta CrystallineSemistableComparison.CH.term CrystallineSemistableComparison.E.Res.dvC
  exact (hT.dv_nat s _ _).symm

theorem dvC_cupC (μ : ResPair T₁ T₂ T₃ P) (h₁ : T₁.Good) (h₂ : T₂.Good) {s t r k : ℕ} (h : s + t = r)
    (a : Cn (T₁.K s) k) (y : Cn (T₂.K t) 0) (hy : T₂.dvC t 0 y = 0) :
    T₃.dvC r k ((μ.μ s t r h).cupC (add_zero k) a y) =
      (μ.μ (s + 1) t (r + 1) (by omega)).cupC (add_zero k) (T₁.dvC s k a) y := by
  delta CrystallineSemistableComparison.E.Res.dvC CrystallineSemistableComparison.CH.Pairing.cupC
  funext σ
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mk₂_apply]
  have hz : ∀ (g : Fin (0 + 1) → Fin (k + 1)) (hg : Monotone g),
      CrystallineSemistableComparison.CH.term (T₂.K (t + 1)) σ (0 : Cn (T₂.K (t + 1)) 0) g hg = 0 := fun g hg => by
    delta CrystallineSemistableComparison.CH.term
    exact map_zero _
  rw [μ.leib, ← term_dvC h₂ σ y, hy, hz, map_zero, smul_zero, add_zero, ← term_dvC h₁ σ a]
  rfl

theorem stCupA : CrystallineSemistableComparison.E.CupLeib.{1} → CrystallineSemistableComparison.E.StCupA := by
  intro hL R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ h₁ h₂ i t n z y u hy hdy hst s
  induction s with
  | zero =>
    intro k r h x hx
    obtain ⟨hik, rfl⟩ := hx
    subst hik
    obtain rfl : r = t := by omega
    exact hst
  | succ s ih =>
    intro k r h x hx
    obtain ⟨a, rfl, hsa⟩ := hx
    obtain rfl : r = s + t + 1 := by omega
    show ∃ a', T₃.dvC (s + t) k a' = _ ∧
      T₃.St u (s + t) (k + 1) ((-1) ^ k • CrystallineSemistableComparison.CH.d (T₃.K (s + t)) k a')
    refine ⟨(μ.μ s t (s + t) rfl).cupC (add_zero k) a y, dvC_cupC μ h₁ h₂ rfl a y hy, ?_⟩
    have hcup := hL R C (T₁.K s) (T₂.K t) (T₃.K (s + t)) (μ.μ s t (s + t) rfl) k 0 k (add_zero k) a y
    rw [hcup, hdy, map_zero, smul_zero, add_zero, ← LinearMap.smul_apply, ← map_zsmul]
    exact ih (k + 1) (s + t) rfl _ hsa

end GlobalTheory.CompanionTheory.StairCupFirst
end

