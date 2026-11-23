module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPtsHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lPts_holds :
    LGrp → LPts := by
  intro hLG E _ Γ _ X O _ _ K K₀ K₁ KN M N Y Y' pY π π' s a b hKN hNK hN0 h10 hπ hQ0 hQ1 hcomm
    hcov b₀ hb₀ Ω _ _ z y' hy'
  subst hKN
  have hMN : X.K M ≤ X.K N := fun v hv => by simpa using b v hv
  have hM1 : X.K M ≤ K₁ := hQ1.le
  have ad := hQ0.adm
  have hnorm : ∀ g ∈ K₀, ∀ v ∈ X.K M, g * v * g⁻¹ ∈ X.K M := fun g hg => (ad g hg).2
  have trc : ∀ g g' (e : g = g') a b a' b', X.tr M M g a b = X.tr M M g' a' b' := by
    intro g g' e a b a' b'
    subst e
    rfl
  have trm : ∀ g g' (hg : g ∈ K₀) (hg' : g' ∈ K₀) a b a' b',
      X.tr M M g a b ≫ X.tr M M g' a' b' =
        X.tr M M (g' * g) (ad _ (K₀.mul_mem hg' hg)).1 (ad _ (K₀.mul_mem hg' hg)).2 :=
    fun g g' hg hg' a b a' b' => X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  haveI := X.onto M N a b
  haveI := X.fin M N a b
  haveI := X.etale M N a b
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (X.tr M N 1 a b) z
  obtain ⟨x₁, hx₁⟩ := hQ1.onto Ω y' (z ≫ X.q N)
    (by rw [← Category.assoc, hy', Category.assoc, hπ, ← Category.assoc])
  obtain ⟨u, hu, au, bu, hx₁u⟩ := hQ0.fib Ω x₀ x₁ (by
    have e1 : x₀ ≫ π' ≫ s = z ≫ π := by rw [← hcomm, ← Category.assoc, ← hx₀]
    have e2 : x₁ ≫ π' ≫ s = z ≫ π := by rw [← Category.assoc, hx₁, hy']
    rw [e1, e2])
  have cond : ∀ h (hh : h ∈ K₀) a' b', x₀ ≫ X.tr M M h a' b' ≫ π' = y' ↔ h * u⁻¹ ∈ K₁ := by
    intro h hh a' b'
    constructor
    · intro hy
      have e : x₀ ≫ X.tr M M u au bu ≫ π' = x₀ ≫ X.tr M M h a' b' ≫ π' := by
        rw [hy, ← hx₁, hx₁u, Category.assoc]
      obtain ⟨w, hw, aw, bw, hw'⟩ := hQ1.fib Ω (x₀ ≫ X.tr M M u au bu) (x₀ ≫ X.tr M M h a' b')
        (by simpa only [Category.assoc] using e)
      have hwu : w * u ∈ K₀ := K₀.mul_mem (h10 hw) hu
      have e2 : x₀ ≫ X.tr M M h a' b' = x₀ ≫ X.tr M M (w * u) (ad _ hwu).1 (ad _ hwu).2 := by
        rw [hw', Category.assoc, trm _ _ hu (h10 hw)]
      have hk : h * (w * u)⁻¹ ∈ K₀ := K₀.mul_mem hh (K₀.inv_mem hwu)
      have e3 : (x₀ ≫ X.tr M M (w * u) (ad _ hwu).1 (ad _ hwu).2) ≫
          X.tr M M (h * (w * u)⁻¹) (ad _ hk).1 (ad _ hk).2 =
            x₀ ≫ X.tr M M (w * u) (ad _ hwu).1 (ad _ hwu).2 := by
        rw [Category.assoc, trm _ _ hwu hk, ← e2]
        congr 1
        exact trc _ _ (by group) _ _ _ _
      have hin := hQ0.free _ hk _ _ Ω _ e3
      have h2 : h * u⁻¹ = (h * (w * u)⁻¹) * w := by group
      rw [h2]
      exact K₁.mul_mem (hM1 hin) hw
    · intro hw
      have hw0 : h * u⁻¹ ∈ K₀ := h10 hw
      have e : X.tr M M u au bu ≫ X.tr M M (h * u⁻¹) (ad _ hw0).1 (ad _ hw0).2 ≫ π' =
          X.tr M M h a' b' ≫ π' := by
        rw [← Category.assoc, trm _ _ hu hw0]
        congr 1
        exact trc _ _ (by group) _ _ _ _
      rw [hQ1.inv _ hw] at e
      rw [← hx₁, hx₁u, Category.assoc, e]
  have trg : ∀ i j (g g' : Γ) (e : g = g') a b a' b', X.tr i j g a b = X.tr i j g' a' b' := by
    intro i j g g' e a b a' b'
    subst e
    rfl
  have fibk : ∀ k ∈ X.K N, ∀ a' b', X.tr M M k a' b' ≫ X.tr M N 1 a b = X.tr M N 1 a b := by
    intro k hk a' b'
    have ak : k ∈ X.Δ := X.K_le N k hk
    have bk : ∀ v ∈ X.K N, k * v * k⁻¹ ∈ X.K N := fun v hv =>
      (X.K N).mul_mem ((X.K N).mul_mem hk hv) ((X.K N).inv_mem hk)
    have a1 : 1 * k ∈ X.Δ := by simpa using ak
    have b1 : ∀ v ∈ X.K M, 1 * k * v * (1 * k)⁻¹ ∈ X.K N := fun v hv =>
      hMN (by simpa using hnorm k (hN0 hk) v hv)
    have a2 : k * 1 ∈ X.Δ := by simpa using ak
    have b2 : ∀ v ∈ X.K M, k * 1 * v * (k * 1)⁻¹ ∈ X.K N := fun v hv =>
      hMN (by simpa using hnorm k (hN0 hk) v hv)
    rw [X.tr_mul M M N k 1 a' b' a b a1 b1, trg M N _ _ (by group) a1 b1 a2 b2,
      ← X.tr_mul M N N 1 k a b ak bk a2 b2, X.tr_self N k ak bk hk, Category.comp_id]
  have kN : ∀ n : ↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N), ((Quotient.out n : X.K N) : Γ) ∈ K₀ :=
    fun n => hN0 (Quotient.out n).2
  obtain ⟨φ, hφdef⟩ : ∃ φ : (↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N)) → (sp Ω ⟶ X.Z M),
      ∀ n, φ n = x₀ ≫ X.tr M M ((Quotient.out n : X.K N) : Γ) (ad _ (kN n)).1 (ad _ (kN n)).2 :=
    ⟨_, fun n => rfl⟩
  have hF : ∀ (c : ↥K ⧸ (X.K N).subgroupOf K) (n : ↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N)),
      b₀⁻¹ * ↑(Quotient.out c) * ↑(Quotient.out n) * u⁻¹ ∈ K₁ →
      φ n ≫ X.tr M N 1 a b = z ∧ b₀⁻¹ * ↑(Quotient.out c) ∈ K₀ ∧
        ∀ (a' : b₀⁻¹ * ↑(Quotient.out c) ∈ X.Δ)
          (b' : ∀ v ∈ X.K M, b₀⁻¹ * ↑(Quotient.out c) * v * (b₀⁻¹ * ↑(Quotient.out c))⁻¹ ∈ X.K M),
          φ n ≫ X.tr M M (b₀⁻¹ * ↑(Quotient.out c)) a' b' ≫ π' = y' := by
    intro c n hcn
    have hn0 := kN n
    have hg : b₀⁻¹ * ↑(Quotient.out c) ∈ K₀ := by
      have e : b₀⁻¹ * ↑(Quotient.out c) = (b₀⁻¹ * ↑(Quotient.out c) * ↑(Quotient.out n) * u⁻¹) * u *
          (↑(Quotient.out n))⁻¹ := by group
      rw [e]
      exact K₀.mul_mem (K₀.mul_mem (h10 hcn) hu) (K₀.inv_mem hn0)
    refine ⟨?_, hg, fun a' b' => ?_⟩
    · rw [hφdef, Category.assoc, fibk _ (Quotient.out n).2, hx₀]
    · rw [hφdef, Category.assoc, ← Category.assoc (X.tr M M _ _ _), trm _ _ hn0 hg]
      exact (cond _ (K₀.mul_mem hg hn0) _ _).2 hcn
  rw [← hLG Γ K K₀ K₁ (X.K N) (X.K M) hMN hNK hN0 hM1 h10 hnorm hcov b₀ hb₀ u hu]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun cn => ⟨(cn.1.1, φ cn.1.2), hF cn.1.1 cn.1.2 cn.2⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨c1, n1⟩, h1⟩ ⟨⟨c2, n2⟩, h2⟩ hE
    have hc : c1 = c2 := congrArg (fun t => t.1.1) hE
    have hx : φ n1 = φ n2 := congrArg (fun t => t.1.2) hE
    subst hc
    have hn : n1 = n2 := by
      have hk1 := kN n1
      have hk2 := kN n2
      have hd : ((Quotient.out n2 : X.K N) : Γ) * ((Quotient.out n1 : X.K N) : Γ)⁻¹ ∈ K₀ :=
        K₀.mul_mem hk2 (K₀.inv_mem hk1)
      have e3 : φ n1 ≫ X.tr M M _ (ad _ hd).1 (ad _ hd).2 = φ n1 := by
        conv_rhs => rw [hx]
        rw [hφdef, hφdef, Category.assoc, trm _ _ hk1 hd]
        congr 1
        exact trc _ _ (by group) _ _ _ _
      have hdM := hQ0.free _ hd _ _ Ω _ e3
      rw [← QuotientGroup.out_eq' n1, ← QuotientGroup.out_eq' n2, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have e4 : (((Quotient.out n1)⁻¹ * Quotient.out n2 : X.K N) : Γ) =
          ((Quotient.out n1 : X.K N) : Γ)⁻¹ *
            (((Quotient.out n2 : X.K N) : Γ) * ((Quotient.out n1 : X.K N) : Γ)⁻¹) *
              ((Quotient.out n1 : X.K N) : Γ)⁻¹⁻¹ := by
        push_cast
        group
      rw [e4]
      exact hnorm _ (K₀.inv_mem hk1) _ hdM
    subst hn
    rfl
  · rintro ⟨⟨c, x⟩, hx, hg, hy⟩
    dsimp only at hx hg hy
    obtain ⟨k, hk, ak, bk, hxk⟩ := X.trans M N a b (fun k hk v hv => hnorm k (hN0 hk) v hv) Ω x₀ x
      (by rw [hx, hx₀])
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((X.K M).subgroupOf (X.K N)) (⟨k, hk⟩ : X.K N)
    have hφ : φ (QuotientGroup.mk ⟨k, hk⟩) = x := by
      rw [hxk, hφdef]
      have hmM : ((m : X.K N) : Γ) ∈ X.K M := Subgroup.mem_subgroupOf.mp m.2
      have hmK0 : ((m : X.K N) : Γ) ∈ K₀ := hN0 (hMN hmM)
      have e : ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : ↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N)) :
          X.K N) : Γ) = k * ((m : X.K N) : Γ) := by
        rw [hm]
        rfl
      congr 1
      rw [trc _ _ e _ _ (ad _ (K₀.mul_mem (hN0 hk) hmK0)).1 (ad _ (K₀.mul_mem (hN0 hk) hmK0)).2,
        ← trm _ _ hmK0 (hN0 hk) (ad _ hmK0).1 (ad _ hmK0).2 ak bk, X.tr_self M _ _ _ hmM,
        Category.id_comp]
    have hn0 := kN (QuotientGroup.mk ⟨k, hk⟩ : ↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N))
    have hyy := hy (ad _ hg).1 (ad _ hg).2
    rw [← hφ, hφdef] at hyy
    have hmem := (cond _ (K₀.mul_mem hg hn0) (ad _ (K₀.mul_mem hg hn0)).1
      (ad _ (K₀.mul_mem hg hn0)).2).1 (by
        rw [← trm _ _ hn0 hg]
        simpa only [Category.assoc] using hyy)
    refine ⟨⟨(c, QuotientGroup.mk ⟨k, hk⟩), hmem⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hφ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiesAbsOf
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem desc_sq {I B : Type} {W Z Y Y' : Scheme.{0}} (cls : I → B) (f : I → (W ⟶ Z)) (kc : I → (W ⟶ Y')) (π : Z ⟶ Y) (t : B → (Y' ⟶ Y))
    (h : ∀ c, f c ≫ π = kc c ≫ t (cls c)) :
    Sigma.desc f ≫ π = (Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c)) ≫ Sigma.desc t := by
  refine Limits.Sigma.hom_ext _ _ fun c => ?_
  simp only [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, Category.assoc, h]

set_option maxHeartbeats 200000 in
theorem liesAbs_of (hP : LPts) (hC : LCount) (hI : LIdx) (hS : SigmaFEt) : LiesAbs := by
  intro p _ D G L E _ _ gb k T N J A _ g θ O _ _ C j K₀ K₁ Y' π' s d hK hN hq0 hq1 hc hs hcos ht
  have trc : ∀ {i i' : T.X.ι} (x y : G.GAf) (e : x = y) (a : x ∈ T.X.Δ)
      (b : ∀ u ∈ T.X.K i, x * u * x⁻¹ ∈ T.X.K i') (a' : y ∈ T.X.Δ)
      (b' : ∀ u ∈ T.X.K i, y * u * y⁻¹ ∈ T.X.K i'), T.X.tr i i' x a b = T.X.tr i i' y a' b' := by
    intro i i' x y e a b a' b'
    subst e
    rfl
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have hMpos : 0 < ((g j).M : ℕ) := by
    have := (g j).M.2.1
    omega
  have hNK : (L.KN (N : ℕ)).relIndex (g j).K ≠ 0 := by
    have h1 := hI p D G L (N : ℕ) hNpos
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (g j).le (g j).le_one] at h1
    exact left_ne_zero_of_mul h1
  have hK0 : K₀.relIndex (g j).K ≠ 0 := fun h0 => hNK (Subgroup.relIndex_eq_zero_of_le_left hN h0)
  haveI : Finite (g j).I := by
    haveI : ((L.KN (N : ℕ)).subgroupOf (g j).K).FiniteIndex := ⟨hNK⟩
    show Finite (↥(g j).K ⧸ (L.KN (N : ℕ)).subgroupOf (g j).K)
    infer_instance
  haveI : Finite (↥(g j).K ⧸ K₀.subgroupOf (g j).K) := by
    haveI : (K₀.subgroupOf (g j).K).FiniteIndex := ⟨hK0⟩
    infer_instance
  have hm0 : (T.X.K (T.lev (g j).M)).relIndex ((g j).K ⊓ K₁) ≠ 0 := by
    have hle1 : T.X.K (T.lev (g j).M) ≤ (g j).K ⊓ K₁ := by
      refine le_inf ?_ hq1.le
      rw [T.K_eq]
      exact (KN_anti (g j).dvd).trans (g j).le
    have hle2 : (g j).K ⊓ K₁ ≤ L.KN 1 := inf_le_left.trans (g j).le_one
    have h1 := hI p D G L ((g j).M : ℕ) hMpos
    rw [← T.K_eq, ← Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2] at h1
    exact left_ne_zero_of_mul h1
  have a1 : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have b1 : ∀ u ∈ T.X.K (T.lev (g j).M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N) := by
    intro u hu
    rw [T.K_eq] at hu ⊢
    simpa using KN_anti (g j).dvd hu
  have aH : ∀ x ∈ (g j).K, (g j).h * x ∈ T.X.Δ := fun x hx =>
    (T.Δ_eq _).2 ((g j).int.mul (integ_of_mem ((g j).le_one hx)))
  have bH : ∀ x ∈ (g j).K, ∀ u ∈ T.X.K (T.lev (g j).M),
      (g j).h * x * u * ((g j).h * x)⁻¹ ∈ T.X.K (T.lev N) := by
    intro x hx u hu
    rw [T.K_eq] at hu ⊢
    exact (g j).adm x hx u hu
  let cls : (g j).I → ↥(g j).K ⧸ K₀.subgroupOf (g j).K := fun c => QuotientGroup.mk (Quotient.out c)
  let u : (g j).I → G.GAf := fun c => (↑(Quotient.out (cls c)) : G.GAf)⁻¹ * ↑(Quotient.out c)
  have hmem : ∀ c, u c ∈ K₀ := by
    intro c
    have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' (cls c))
    simpa [Subgroup.mem_subgroupOf] using h
  let kc : (g j).I → (T.X.Z (T.lev (g j).M) ⟶ Y') := fun c =>
    T.X.tr _ _ (u c) (hq0.adm _ (hmem c)).1 (hq0.adm _ (hmem c)).2 ≫ π'
  choose tb0 htb1 htb2 using ht
  let tb : (↥(g j).K ⧸ K₀.subgroupOf (g j).K) → (Y' ⟶ C.Y) := fun b => tb0 _ (Quotient.out b).2
  have hsq' : ∀ c, T.X.tr (T.lev (g j).M) (T.lev N) 1 a1 b1 ≫ C.π = kc c ≫ s := by
    intro c
    rw [hc]
    simp only [kc, Category.assoc]
    exact (hq0.inv _ (hmem c) _ _).symm
  have hsq : (T.tower N g).s j ≫ C.π =
      (Limits.Sigma.desc fun c => kc c ≫ Limits.Sigma.ι (fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => Y') (cls c)) ≫
        Limits.Sigma.desc fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => s :=
    desc_sq cls (fun _ => T.X.tr (T.lev (g j).M) (T.lev N) 1 a1 b1) kc C.π (fun _ => s) hsq'
  refine ⟨∐ fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => Y', Limits.Sigma.desc fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => s, Limits.Sigma.desc tb,
    Nat.card (↥(g j).K ⧸ K₀.subgroupOf (g j).K) * d, (T.X.K (T.lev (g j).M)).relIndex ((g j).K ⊓ K₁),
    hS C.Y Y' s d _ hs, ?_, Nat.pos_of_ne_zero hm0, _, hsq, ?_, ?_⟩
  · refine Limits.Sigma.hom_ext _ _ fun b => ?_
    simp only [Limits.Sigma.ι_desc_assoc, tb, htb1]
  · refine Limits.Sigma.hom_ext _ _ fun c => ?_
    show Limits.Sigma.ι _ c ≫ (Limits.Sigma.desc fun c => kc c ≫ Limits.Sigma.ι (fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => Y') (cls c)) ≫ Limits.Sigma.desc tb =
      Limits.Sigma.ι _ c ≫ (Limits.Sigma.desc fun c : (g j).I => T.X.tr (T.lev (g j).M) (T.lev N) ((g j).h * ↑(Quotient.out c)) (aH _ (Quotient.out c).2) (bH _ (Quotient.out c).2)) ≫ C.π
    rw [Limits.Sigma.ι_desc_assoc, Category.assoc, Limits.Sigma.ι_desc]
    erw [Limits.Sigma.ι_desc_assoc]
    have e : (g j).h * ↑(Quotient.out (cls c)) * u c = (g j).h * ↑(Quotient.out c) := by
      show (g j).h * ↑(Quotient.out (cls c)) * ((↑(Quotient.out (cls c)) : G.GAf)⁻¹ * ↑(Quotient.out c)) = _
      rw [_root_.mul_assoc, _root_.mul_inv_cancel_left]
    have key := T.X.tr_mul (T.lev (g j).M) (T.lev (g j).M) (T.lev N) (u c) ((g j).h * ↑(Quotient.out (cls c)))
      (hq0.adm _ (hmem c)).1 (hq0.adm _ (hmem c)).2 (aH _ (Quotient.out (cls c)).2) (bH _ (Quotient.out (cls c)).2)
      (by rw [e]; exact aH _ (Quotient.out c).2) (by rw [e]; exact bH _ (Quotient.out c).2)
    show T.X.tr _ _ (u c) _ _ ≫ π' ≫ tb (cls c) = T.X.tr _ _ ((g j).h * ↑(Quotient.out c)) _ _ ≫ C.π
    rw [show tb (cls c) = tb0 _ (Quotient.out (cls c)).2 from rfl, htb2 _ _ (aH _ (Quotient.out (cls c)).2) (bH _ (Quotient.out (cls c)).2)]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.π) key).trans (congrArg (· ≫ C.π) (trc _ _ e _ _ _ _)))
  · refine hC (g j).I _ _ _ C.Y Y' cls (T.X.tr (T.lev (g j).M) (T.lev N) 1 a1 b1) kc C.π s _
      (T.X.fin _ _ a1 b1) (T.X.etale _ _ a1 b1) hs.1 hs.2.1 ?_ hsq
    intro Ω _ _ z b y' hy
    have hcount := hP E G.GAf T.X O (g j).K K₀ K₁ (L.KN (N : ℕ)) (T.lev (g j).M) (T.lev N) C.Y Y' C.p C.π π' s a1 b1
      (T.K_eq N) (g j).le hN hK C.ov hq0 hq1 (hc a1 b1) hcos (↑(Quotient.out b)) (Quotient.out b).2 Ω z y' hy
    rw [← hcount]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun cx => ?_)
    constructor
    · rintro ⟨h1, rfl, h3⟩
      exact ⟨h1, hmem cx.1, fun a' b' => h3⟩
    · rintro ⟨h1, h2, h3⟩
      have hcl : cls cx.1 = b := by
        rw [← QuotientGroup.out_eq' b]
        refine (QuotientGroup.eq.2 ?_).symm
        simpa [Subgroup.mem_subgroupOf] using h2
      subst hcl
      exact ⟨h1, rfl, h3 _ _⟩

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

def Cg {M : Type} [AddCommGroup M] (n : ℕ) (x y : M) : Prop := ∃ z, x = y + n • z

def MOne : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 →
  Function.Bijective (algebraMap (𝓞 D.F) D.O) ∧ Module.Projective D.O D.La ∧ Module.Finite D.O D.La

def Idem : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∃ ε : ℕ → 𝓞 D.F, ∀ e : ℕ,
  1 - ε e ∈ ES.uIdeal D r ^ e ∧ D.bar (ε e) ∈ ES.uIdeal D r ^ e ∧ (∀ x ∈ ES.uIdeal D r ^ e, (q : 𝓞 D.F) ^ e ∣ ε e * x) ∧
  (q : 𝓞 D.F) ^ e ∣ ε e + D.bar (ε e) - 1 ∧ (q : 𝓞 D.F) ^ e ∣ ε (e + 1) - ε e ∧
  ∀ (𝔞 : Ideal (𝓞 D.F)), (∃ f : ℕ, ES.uIdeal D r ^ f ≤ 𝔞) → (q : 𝓞 D.F) ^ e ∈ 𝔞 → ES.uIdeal D r ^ e ≤ 𝔞

def LiftUnit : Prop := ∀ (A M : Type) [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
  (u 𝔞 : Ideal A), u ≠ ⊥ → (∃ f : ℕ, u ^ f ≤ 𝔞) → ∀ g₀ : (M ⧸ (𝔞 • ⊤ : Submodule A M)) ≃ₗ[A] (M ⧸ (𝔞 • ⊤ : Submodule A M)),
  ∃ (g : M →ₗ[A] M) (h : ℕ → (M →ₗ[A] M)), (∀ x, (𝔞 • ⊤ : Submodule A M).mkQ (g x) = g₀ ((𝔞 • ⊤ : Submodule A M).mkQ x)) ∧
    ∀ e x, g (h e x) - x ∈ (u ^ e • ⊤ : Submodule A M) ∧ h e (g x) - x ∈ (u ^ e • ⊤ : Submodule A M)

def Adj : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (e : ℕ), (∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0) ∧
  (∀ h : D.La →ₗ[D.O] D.La, ∃ k : D.La →+ D.La, (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (h x) y - D.EF x (k y)) ∧
    ∀ (c : D.O) y, Cg (q ^ e) (k (c • y)) (c • k y)) ∧
  ∀ g : D.La →+ D.La, (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (g x) (g y) - D.EF x y) →
    (∀ x, Cg (q ^ e) (g x) 0 → Cg (q ^ e) x 0) ∧ ∀ x, ∃ y, Cg (q ^ e) (g y) x

def QSys : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∀ (𝔞 : Ideal (𝓞 D.F)),
  (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) → ∀ g₀ : LevGrp D 𝔞 1, ∃ g : ℕ → D.La →+ D.La, ∀ e : ℕ,
    (∀ (c : D.O) x, Cg (q ^ e) (g e (c • x)) (c • g e x)) ∧ (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (g e x) (g e y) - D.EF x y) ∧
    (∀ x, Cg (q ^ e) (g (e + 1) x) (g e x)) ∧ ((q : 𝓞 D.F) ^ e ∈ 𝔞 → ∀ x, (wSub D 𝔞 1).mkQ (g e x) = g₀ ((wSub D 𝔞 1).mkQ x))

structure IsSys {G : GDatum} (g : ℕ → G.La →+ G.La) : Prop where
  lin : ∀ n, 0 < n → ∀ (c : G.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  onto : ∀ n, 0 < n → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → ∀ x z, g n x = n • z → ∃ v, x = n • v
  iso : ∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ G.EF (g n x) (g n y) - G.EF x y
  tow : ∀ n m, 0 < n → 0 < m → ∀ x, ∃ z, g (n * m) x = g n x + n • z

def TResim : Prop := ∀ (G : GDatum) (k : Type) [Field k] (Q : Type) [Group Q] (act : G.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop)
  (I : GTateIso G k Q act e) (g : ℕ → G.La →+ G.La), IsSys g → ∃ I' : GTateIso G k Q act e, ∀ n, 0 < n → ∀ x, I'.ev n x = I.ev n (g n x)

def OResim : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R)
  (gb : GBase D.toG R') (N N₀ c : ℕ), N = N₀ * c → 0 < N → ∀ (X X₁ : Scheme.{0}) (s : X ⟶ Sp R') (s₁ : X₁ ⟶ Sp R) (o : GObj gb N s)
  (u : Obj b N₀ s₁) (f : X ⟶ X₁) (n : QMap o u f c) (g : ℕ → D.La →+ D.La), IsSys (G := D.toG) g → (∀ x, ∃ z, g N₀ x = x + N₀ • z) →
  ∃ (o' : GObj gb N s) (n' : QMap o' u f c), ∀ y : D.La, (o'.eta y).left ≫ n'.φ = (o.eta (g N y)).left ≫ n.φ

def TExt : Prop := ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase G R) (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
  (σ : Sp Ω ⟶ Sp R) (o : GObj gb N σ)
  (I : GTateIso G Ω (Over.mk (𝟙 (Sp Ω)) ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)))
  (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp Ω),
  ∃ I' : GTateIso G k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ n, 0 < n → ∀ y, (I'.ev n y).left = x ≫ (I.ev n y).left

def Raise : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R)
  (gb : GBase D.toG R') (β : R →+* R'), Match b gb β → ∀ (N N₀ c : ℕ), N = N₀ * c → 0 < N → N₀.Coprime q →
  ∀ (X₁ : Scheme.{0}) (s₁ : X₁ ⟶ Sp R) (u : Obj b N₀ s₁) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ X₁) (σ : Sp Ω ⟶ Sp R'),
  y ≫ s₁ = σ ≫ spMap β → ∃ o : GObj gb N σ, Nonempty (QMap o u y c)

def ClsAt : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm →
  ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (β : R →+* R'), Match b gb β →
  ∀ (N N₀ c : ℕ) (a : 𝓞 D.F) (𝔞 : Ideal (𝓞 D.F)), N = N₀ * c → 0 < N → N₀.Coprime q → IsGen a N 𝔞 → (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) →
  ∀ (Y : EtModel b N₀ 𝔞 1) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Y.X) (σ : Sp Ω ⟶ Sp R'), y ≫ Y.s = σ ≫ spMap β →
  ∃ (o : GObj gb N σ) (C : Cls Y β o c a), C.j = y

def EpsEx : Prop := ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [CharZero A] (𝔟₁ 𝔟₂ : Ideal A) (a₁ a₂ : A) (M₁ M₂ t : ℕ), 0 < M₁ →
  M₁ = M₂ * t → 𝔟₁ ≤ 𝔟₂ → IsGen a₁ M₁ 𝔟₁ → IsGen a₂ M₂ 𝔟₂ → ∃ ε : A, (M₁ : A) ∣ ε * a₁ - t * a₂ ∧ (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁

def LevDown : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R)
  (o : Obj b N s) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (ε : 𝓞 D.F), 𝔟₁ ≠ ⊥ → (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁ → ∀ l : D.La → (𝟙_ (Over S) ⟶ o.A),
  IsEtLev o 𝔟₁ 1 l → IsEtLev o 𝔟₂ 1 fun y => l (algebraMap (𝓞 D.F) D.O ε • y)

def DownEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → D.a = 1 → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
  (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫)
  (N₀ κ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S (N₀ * κ) 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (ε : 𝓞 D.F), (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁ →
  ∃ (t : X₁.Y.X ⟶ X₂.Y.X) (m : ObjMap (X₁.Y.univ.forget N₀ (Dvd.intro _ rfl) X₁.lev.2.1) X₂.Y.univ t), t ≫ X₂.Y.s = X₁.Y.s ∧ IsFinite t ∧ Etale t ∧
    ∀ y : D.La, (X₁.Y.lv (algebraMap (𝓞 D.F) D.O ε • y)).left ≫ m.φ = t ≫ (X₂.Y.lv y).left

end UpperTheory.Gal.FiniteEtaleModels.O
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PBaseFet
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels

private theorem of_section {𝒞 : Type*} [Category 𝒞] [HasPullbacks 𝒞] (W : MorphismProperty 𝒞) [W.IsStableUnderBaseChange]
    {Y X P P' Z B V : 𝒞} (pk : P ⟶ Y) (pk' : P' ⟶ X) (j : X ⟶ Y) (pw : P' ⟶ P) (hp : IsPullback pw pk' pk j)
    (ε : Y ⟶ P) (hε : ε ≫ pk = 𝟙 Y) (sY : Y ⟶ B) (g : V ⟶ B) (sX : X ⟶ V) (ov : j ≫ sY = sX ≫ g)
    (e : Z ≅ P') (q : Z ⟶ V) (hq : e.hom ≫ pk' ≫ sX = q) (h : (e.hom ≫ pw) ≫ pk ≫ sY = q ≫ g)
    (hF : W (pullback.lift (e.hom ≫ pw) q h)) : W (pullback.lift j sX ov) := by
  have hε' : (j ≫ ε) ≫ pk = 𝟙 X ≫ j := by simp [hε]
  let ε₀ : X ⟶ P' := hp.lift (j ≫ ε) (𝟙 X) hε'
  have h₁ : ε₀ ≫ pw = j ≫ ε := hp.lift_fst _ _ _
  have h₂ : ε₀ ≫ pk' = 𝟙 X := hp.lift_snd _ _ _
  have hE : (pullback.fst sY g ≫ ε) ≫ pk ≫ sY = pullback.snd sY g ≫ g := by
    rw [Category.assoc, reassoc_of% hε, pullback.condition]
  let εE : pullback sY g ⟶ pullback (pk ≫ sY) g := pullback.lift (pullback.fst sY g ≫ ε) (pullback.snd sY g) hE
  have F₁ : pullback.lift (e.hom ≫ pw) q h ≫ pullback.fst _ _ = e.hom ≫ pw := pullback.lift_fst _ _ _
  have F₂ : pullback.lift (e.hom ≫ pw) q h ≫ pullback.snd _ _ = q := pullback.lift_snd _ _ _
  have f₁ : pullback.lift j sX ov ≫ pullback.fst _ _ = j := pullback.lift_fst _ _ _
  have f₂ : pullback.lift j sX ov ≫ pullback.snd _ _ = sX := pullback.lift_snd _ _ _
  have E₁ : εE ≫ pullback.fst _ _ = pullback.fst sY g ≫ ε := pullback.lift_fst _ _ _
  have E₂ : εE ≫ pullback.snd _ _ = pullback.snd sY g := pullback.lift_snd _ _ _
  have sq : IsPullback (ε₀ ≫ e.inv) (pullback.lift j sX ov) (pullback.lift (e.hom ≫ pw) q h) εE := by
    have hcomm : (ε₀ ≫ e.inv) ≫ pullback.lift (e.hom ≫ pw) q h = pullback.lift j sX ov ≫ εE := by
      apply pullback.hom_ext
      · simp only [Category.assoc, F₁, E₁, Iso.inv_hom_id_assoc, h₁]
        rw [reassoc_of% f₁]
      · simp only [Category.assoc, F₂, E₂, f₂]
        rw [← hq, Iso.inv_hom_id_assoc, reassoc_of% h₂]
    refine ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ e.hom ≫ pk') ?_ ?_ ?_⟩⟩
    · intro s
      have c := s.condition
      have c₁ : s.fst ≫ e.hom ≫ pw = s.snd ≫ pullback.fst sY g ≫ ε := by
        simpa only [Category.assoc, F₁, E₁] using c =≫ pullback.fst _ _
      have c₃ : s.fst ≫ e.hom ≫ pk' ≫ j = s.snd ≫ pullback.fst sY g := by
        have := c₁ =≫ pk
        simpa only [Category.assoc, hp.w, hε, Category.comp_id] using this
      have key : (s.fst ≫ e.hom ≫ pk') ≫ ε₀ = s.fst ≫ e.hom := by
        apply hp.hom_ext
        · simp only [Category.assoc, h₁]
          rw [reassoc_of% c₃, c₁]
        · simp only [Category.assoc, h₂, Category.comp_id]
      rw [← Category.assoc, key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro s
      have c := s.condition
      have c₁ : s.fst ≫ e.hom ≫ pw = s.snd ≫ pullback.fst sY g ≫ ε := by
        simpa only [Category.assoc, F₁, E₁] using c =≫ pullback.fst _ _
      have c₂ : s.fst ≫ q = s.snd ≫ pullback.snd sY g := by
        simpa only [Category.assoc, F₂, E₂] using c =≫ pullback.snd _ _
      have c₃ : s.fst ≫ e.hom ≫ pk' ≫ j = s.snd ≫ pullback.fst sY g := by
        have := c₁ =≫ pk
        simpa only [Category.assoc, hp.w, hε, Category.comp_id] using this
      apply pullback.hom_ext
      · simpa only [Category.assoc, f₁] using c₃
      · simp only [Category.assoc, f₂]
        rw [hq]; exact c₂
    · intro s m h₃ _
      have := h₃ =≫ (e.hom ≫ pk')
      simp only [Category.assoc, Iso.inv_hom_id_assoc, h₂, Category.comp_id] at this
      exact this
  exact MorphismProperty.of_isPullback sq hF

theorem baseFet_holds : PowCart → PiFet → BaseFet := by
  intro hPow hPi p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T M c a hN C
  obtain ⟨e, hfin, het⟩ := hPi p D G L E gb w q r 𝔴 𝔫 S k T M c a hN C
  have hp : IsPullback (C.pw k) (GlobalTheory.KS.pow (T.M M).univ.A k).hom (GlobalTheory.KS.pow S.Y.univ.A k).hom C.j :=
    ((hPow _ _ _ _ _ _ C.j (𝟙 _) C.m.φ (𝟙 _) C.m.cart.1.w (by simp) k).1 C.m.cart.1)
  let ε : S.Y.X ⟶ (GlobalTheory.KS.pow S.Y.univ.A k).left :=
    (Pi.lift (fun _ : Fin k => (1 : 𝟙_ (Over S.Y.X) ⟶ S.Y.univ.A))).left
  have hε : ε ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = 𝟙 _ := Over.w (Pi.lift (fun _ : Fin k => (1 : 𝟙_ (Over S.Y.X) ⟶ S.Y.univ.A)))
  have key : ∀ (W : MorphismProperty Scheme.{0}) [W.IsStableUnderBaseChange],
      W (pullback.lift (S.pi T C) (T.X.q _) e) → W (pullback.lift C.j (T.M M).s C.ov) := fun W _ hF =>
    of_section W _ _ C.j (C.pw k) hp ε hε S.Y.s (gen (Ow w) E) (T.M M).s C.ov (T.e M) _ (T.e_q M) e hF
  exact ⟨key @IsFinite hfin, key @Etale het⟩

end UpperTheory.Gal.FiniteEtaleModels
end
end

