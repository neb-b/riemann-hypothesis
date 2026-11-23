module

public import Development.EtaleCohomology.TateTwists.Bundle0013
public import Development.EtaleCohomology.TateTwists.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0008
public import Development.EtaleCohomology.TateTwists.Bundle0011
public import Development.EtaleCohomology.TateTwists.Bundle0014
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.TateTwists.Bundle0009

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.CcCupFlipPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.cc_cup_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def LateralTheory.EtaleFoundations.cc_aw_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ}
    (h : n + m = k) (h' : m + n = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW h α.1 β.1 γ.1 → ν.IsAW h' β.1 α.1 γ'.1 →
      CohomologyClass.mk γ = (n * m).negOnePow • CohomologyClass.mk γ'
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipAwExistsPfCochain
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_ev_mk : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
    (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
      ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x

def cupflip_ev_res : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h
    (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g)

def cupflip_sub_res : Prop :=
  ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) {V : Scheme.{0}} (g : V ⟶ U),
    (x.res g).sub j l h = (x.sub j l h).res g

theorem cupflip_aw_cochain_of (hm : cupflip_ev_mk) (he : cupflip_ev_res) (hs : cupflip_sub_res) :
    cupflip_aw_cochain := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hm R (E := E) (I := K) (n := k)
    (fun N w h U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n)
      (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev (R := R) α p _ rfl U (x.sub 0 p (by omega))) (ev (R := R) β (N - p) _ rfl U (x.sub p (N - p) (by omega))))
    (by
      intro N w h V U g x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Sec.res, map_sum, Units.smul_def, map_zsmul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      congr 1
      have := μ.nat g (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
        (ev (R := R) α p _ rfl U (x.sub 0 p (by omega))) (ev (R := R) β (N - p) _ rfl U (x.sub p (N - p) (by omega)))
      simp only [Sec.res] at this
      rw [this]
      have e1 := he R α p _ rfl V U g (x.sub 0 p (by omega))
      have e2 := he R β (N - p) _ rfl V U g (x.sub p (N - p) (by omega))
      simp only [Sec.res] at e1 e2
      rw [e1, e2, hs, hs])
  exact ⟨γ, fun N w h U x => hγ N w h U x⟩

theorem cupflip_sub_res_holds : cupflip_sub_res := by
  intro E U N x j l h V g
  simp only [Sx.res, Sx.sub]
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

theorem freeGen_res {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have key := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op
    (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x))
  simp only [freeGen]
  erw [← key]
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipHomotopyPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations

def phiT {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) {N : ℕ} {U : Scheme.{0}}
    (x : Sx E N U) (w : ℤ) (z : Pr N) : Sec (K.X w) U :=
  if h : -((z.1 : ℤ) + (z.2.1 : ℤ)) + k = w then
    ((m * (z.1 : ℤ)).negOnePow : ℤ) • μ.mul U (-(z.1 : ℤ) + n) (-(z.2.1 : ℤ) + m) w (by omega)
      (ev (R := R) α z.1 _ rfl U (x.along z.2.2.1)) (ev (R := R) β z.2.1 _ rfl U (x.along z.2.2.2))
  else 0

def phi {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) {N : ℕ} {U : Scheme.{0}}
    (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) : Sec (K.X w) U :=
  c.sum fun z a => a • phiT μ hk α β x w z

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (R := R) (α - β) p s h U x = ev (R := R) α p s h U x - ev (R := R) β p s h U x := by
  simp [ev, Cochain.sub_v, Preadditive.comp_sub]
  rfl

theorem ev_zsmul' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x
    (c : ℤ) : ev (R := R) (c • α) p s h U x = c • ev (R := R) α p s h U x := by
  simp [ev, Cochain.smul_v, Linear.comp_smul]
  rfl

def cupflip_ev_ext : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    ∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) → α = β

def cupflip_eta_mk : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ η : Cochain ((chains R).obj E) K (k - 1), ∀ N s hs U x, ev (R := R) η N s hs U x = phi μ hk α β x s (h N)

def cupflip_eta_delta : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (η : Cochain ((chains R).obj E) K (k - 1)),
    (∀ N s hs U x, ev (R := R) η N s hs U x = phi μ hk α.1 β.1 x s (h N)) →
    ∀ N t ht U x, ev (R := R) (δ (k - 1) k η) N t ht U x =
      (k.negOnePow : ℤ) • (phi μ hk α.1 β.1 x t (Pr.aw N) - phi μ hk α.1 β.1 x t (Pr.wa N))

theorem phi_aw {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
    (hγ : μ.IsAW hk α β γ) (N : ℕ) (t : ℤ) (ht : -(N : ℤ) + k = t) (U : Scheme.{0}) (x : Sx E N U) :
    phi μ hk α β x t (Pr.aw N) = ev (R := R) γ N t ht U x := by
  rw [hγ N t ht U x, phi, Pr.aw, ← Finsupp.sum_finsetSum_index (fun z => zero_smul ℤ (phiT μ hk α β x t z))
    (fun z a b => add_smul a b (phiT μ hk α β x t z))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.sum_single_index (zero_smul ℤ (phiT μ hk α β x t _)), one_smul, phiT, dite_eq_left (by have := p.2; push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  rw [Units.smul_def]
  rfl

def cupflip_phi_diag : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (hk' : m + n = k)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)
      (γ' : Cochain ((chains R).obj E) K k), ν.IsAW hk' β α γ' →
      ∀ (N : ℕ) (t : ℤ) (ht : -(N : ℤ) + k = t) (U : Scheme.{0}) (x : Sx E N U),
        phi μ hk α β x t (Pr.wa N) = ((n * m).negOnePow : ℤ) • ev (R := R) γ' N t ht U x

theorem cupflip_phi_diag_pf : cupflip_phi_diag := by
  intro R _ I J K μ ν hflip E n m k hk hk' α β γ' hγ' N t ht U x
  rw [hγ' N t ht U x, phi, Pr.wa, ← Finsupp.sum_finsetSum_index (fun z => zero_smul ℤ (phiT μ hk α β x t z))
    (fun z a b => add_smul a b (phiT μ hk α β x t z)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Finsupp.sum_single_index (zero_smul ℤ (phiT μ hk α β x t _)), phiT,
    dite_eq_left (by push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  rw [hflip U _ _ t (by push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  simp only [Units.smul_def, smul_smul]
  congr 1
  have e : ((-1 : ℤ) ^ ((p : ℕ) * (N - p))) = (((p : ℕ) : ℤ) * ((N - p : ℕ) : ℤ)).negOnePow := by
    rw [Int.negOnePow_def, ← Nat.cast_mul, zpow_natCast]; simp
  rw [e]
  simp only [← Units.val_mul, ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨m * ((N - p : ℕ) : ℤ) - n * m, by ring⟩

theorem cupflip_homotopy_of (hext : cupflip_ev_ext) (hmk : cupflip_eta_mk) (hdl : cupflip_eta_delta) :
    cupflip_homotopy := by
  intro h hs R _ I J K μ ν hflip E n m k hk hk' α β γ γ' hγ hγ'
  obtain ⟨η, hη⟩ := hmk h hs.1 R μ E hk α.1 β.1
  have hd := hdl h hs R μ E hk α β η hη
  refine ⟨((k.negOnePow : ℤˣ) : ℤ) • η, ?_⟩
  rw [show δ (k - 1) k (((k.negOnePow : ℤˣ) : ℤ) • η) = ((k.negOnePow : ℤˣ) : ℤ) • δ (k - 1) k η from
    (δ_hom ℤ _ _ (k - 1) k).map_smul _ _]
  apply hext R
  intro N t ht U x
  have h1 := phi_aw μ hk α.1 β.1 γ.1 hγ N t ht U x
  have h2 := cupflip_phi_diag_pf R μ ν hflip E hk hk' α.1 β.1 γ'.1 hγ' N t ht U x
  rw [ev_zsmul', hd N t ht U x, h1, h2, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul, Units.smul_def, ev_sub', ev_zsmul']

end LateralTheory.EtaleFoundations
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsForPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleAlexanderWhitneyCupCochainExistsForPairing : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def EtaleAlexanderWhitneyCupUniqueBiadditive : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ') ∧
    (∀ (α α' : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) (β β' : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) ∧
    (∀ (β : Cochain ((chains R).obj E) J m), μ.IsAW hk 0 β 0) ∧
    (∀ (α : Cochain ((chains R).obj E) I n), μ.IsAW hk α 0 0)

def EtaleAlexanderWhitneyCupLeibnizRule : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ → δ k k₁ γ = γ₁ + n.negOnePow • γ₂

theorem ev_add' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  unfold ev
  rw [Cochain.add_v, Preadditive.comp_add]
  rfl

theorem ev_zero' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  unfold ev
  rw [Cochain.zero_v, Limits.comp_zero]
  rfl

def EtaleAlexanderWhitneyCupCochainUnique : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ'

theorem awalg_of (hu : EtaleAlexanderWhitneyCupCochainUnique) : EtaleAlexanderWhitneyCupUniqueBiadditive := by
  intro R _ I J K μ E n m k hk
  refine ⟨hu R μ hk, ?_, ?_, ?_, ?_⟩
  · intro α α' β γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add (f := _), LinearMap.add_apply, smul_add]
  · intro α β β' γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add (f := _), smul_add]
  · intro β N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, LinearMap.zero_apply, smul_zero]
  · intro α N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, smul_zero]

theorem cup_spec_part1 (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
    (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 := by
  obtain ⟨γ, hγ⟩ := h1 R μ hk α.1 β.1
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m = k + 1 by omega) (δ n (n + 1) α.1) β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show n + (m + 1) = k + 1 by omega) α.1 (δ m (m + 1) β.1)
  have hd := h3 R μ hk rfl rfl _ _ α.1 β.1 γ γ₁ γ₂ hγ hγ₁ hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₁
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e1, e2, smul_zero, add_zero] at hd
  exact ⟨Cocycle.mk γ (k + 1) rfl hd, hγ⟩

def EtaleAlexanderWhitneyCupDescendsToCohomology : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
        CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

section Desc
variable (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
  {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)

noncomputable def chZ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    Cocycle ((chains R).obj E) K k :=
  Classical.choose (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_spec (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    μ.IsAW hk α.1 β.1 (chZ h1 h2 h3 μ E hk α β).1 :=
  Classical.choose_spec (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_eq (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) : chZ h1 h2 h3 μ E hk α β = γ :=
  Cocycle.ext ((h2 R μ hk).1 _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) h)

theorem chZ_add_left (α α' : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk (α + α') β = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α' β :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α' β))

theorem chZ_add_right (α : Cocycle ((chains R).obj E) I n) (β β' : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk α (β + β') = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α β' :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α β'))

theorem chZ_cob_left (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hα : α ∈ coboundaries _ _ n) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', η, hη⟩ := hα
  obtain ⟨γ, hγ⟩ := h1 R μ (show m' + m = m' + m from rfl) η β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show m' + (m + 1) = k by omega) η (δ m (m + 1) β.1)
  have hd := h3 R μ rfl hm' rfl (show n + m = k from hk) (show m' + (m + 1) = k by omega) η β.1 γ
    (chZ h1 h2 h3 μ E hk α β).1 γ₂ hγ (by rw [hη]; exact chZ_spec h1 h2 h3 μ E hk α β) hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e2, smul_zero, add_zero] at hd
  exact ⟨m' + m, by omega, γ, hd⟩

theorem chZ_cob_right (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hβ : β ∈ coboundaries _ _ m) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', θ, hθ⟩ := hβ
  obtain ⟨γ, hγ⟩ := h1 R μ (show n + m' = n + m' from rfl) α.1 θ
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m' = k by omega) (δ n (n + 1) α.1) θ
  have hd := h3 R μ rfl rfl hm' (show (n + 1) + m' = k by omega) (show n + m = k from hk) α.1 θ γ
    γ₁ (chZ h1 h2 h3 μ E hk α β).1 hγ hγ₁ (by rw [hθ]; exact chZ_spec h1 h2 h3 μ E hk α β)
  rw [Cocycle.δ_eq_zero] at hγ₁
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  rw [e1, zero_add] at hd
  refine ⟨n + m', by omega, n.negOnePow • γ, ?_⟩
  rw [δ_units_smul, hd, smul_smul, Int.units_mul_self, one_smul]

end Desc

theorem desc_of (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule) :
    EtaleAlexanderWhitneyCupDescendsToCohomology := by
  intro R _ I J K μ E n m k hk
  let G : Cocycle ((chains R).obj E) I n → (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    fun α => QuotientAddGroup.lift _
      (AddMonoidHom.mk' (fun β => CohomologyClass.mk (chZ h1 h2 h3 μ E hk α β))
        (fun β β' => by rw [chZ_add_right, CohomologyClass.mk_add]))
      (fun β hβ => by
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
        exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_right h1 h2 h3 μ E hk α β hβ))
  let F : Cocycle ((chains R).obj E) I n →+ (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    AddMonoidHom.mk' G (fun α α' => by
      refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
      show CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
      rw [chZ_add_left, CohomologyClass.mk_add])
  refine ⟨QuotientAddGroup.lift _ F (fun α hα => ?_), ?_⟩
  · rw [AddMonoidHom.mem_ker]
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
    show CohomologyClass.mk _ = 0
    exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_left h1 h2 h3 μ E hk α β hα)
  · intro α β γ hγ
    show CohomologyClass.mk _ = _
    rw [chZ_eq h1 h2 h3 μ E hk α β γ hγ]

theorem etale_cup_compat_spec_of_alexander_whitney_exists_unique_leibniz (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (hu : EtaleAlexanderWhitneyCupCochainUnique)
    (h3 : EtaleAlexanderWhitneyCupLeibnizRule) : EtaleCupCompatAlexanderWhitneyCocycleSpec := by
  have h2 := awalg_of hu
  have h4 := desc_of h1 h2 h3
  intro R _ I J K μ E n m k hk
  refine ⟨fun α β => cup_spec_part1 h1 h2 h3 R μ hk α β, ?_⟩
  intro α β γ hγ
  exact pick_spec (h4 R μ E hk) α β γ hγ
end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCochainComplexBasicPropertiesOfComponents
section
namespace LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
theorem etale_cochain_complex_basic_properties_of_components : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  apply LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := etale_cochain_complex_basic_properties_of_components
end LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupProductFlipExistsOfComponents
section
namespace LateralTheory.Fin.EtaleComplexPairingFlipExists
theorem etale_cup_product_flip_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  apply LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := etale_cup_product_flip_exists_of_components
end LateralTheory.Fin.EtaleComplexPairingFlipExists
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleEvaluationMapConstructionOfComponents
section
namespace LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
theorem etale_evaluation_map_construction_of_components : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  apply LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := etale_evaluation_map_construction_of_components
end LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleFirstChernCochainCoboundaryVanishesSimplexD
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EvDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ}
  (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
  (∀ (x : Sx E 0 U), ev (R := R) (δ n m α) 0 m (by simp) U x =
    Sec.map (I.d n m) (ev (R := R) α 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
    (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
    ev (R := R) (δ n m α) (p + 1) t ht U x =
      Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ev (R := R) α p t (by omega) U (x.face i)

def cx_ext : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n),
  (∀ p s h U x, ev (R := R) α p s h U x = 0) → α = 0

def res_neg : Prop := ∀ (q : ℕ) (s : ℤ), s < 0 → ∀ (U : Scheme.{0}) (a : Sec ((res _ (tw q 1)).X s) U), a = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (R := ZMod q) (δ 2 3 α) 1 2 (by simp) U x = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev (R := ZMod q) (δ 2 3 α) 2 1 (by simp) U x = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 3 U), ev (R := ZMod q) (δ 2 3 α) 3 0 (by simp) U x = 0

theorem etale_first_chern_cochain_closed_of_degree_parts (hd : EvDelta) (hx : cx_ext) (hr : res_neg) (h1 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne) (h2 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo) (h3 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree) :
    EtaleKummerChernClassCochainIsCocycle := by
  intro q _ E L hi α hα
  apply hx
  intro p s h U x
  match p, x with
  | 0, x =>
    obtain rfl : s = 3 := by omega
    rw [(hd (ZMod q) (show (2:ℤ) + 1 = 3 by norm_num) α U).1 x, hα.1 U x]
    exact map_zero ((((res (ZMod q) (tw q 1)).d 2 3).hom.app (op U)).hom)
  | 1, x =>
    obtain rfl : s = 2 := by omega
    exact h1 q L hi α hα U x
  | 2, x =>
    obtain rfl : s = 1 := by omega
    exact h2 q L hi α hα U x
  | 3, x =>
    obtain rfl : s = 0 := by omega
    exact h3 q L hi α hα U x
  | k + 4, x =>
    exact hr q s (by push_cast at h; omega) U _

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etale_first_chern_cochain_closed_of_components (hd : EvDelta) (hx : cx_ext) (hr : res_neg) (h1 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne) (h2 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo) (h3 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree) :
    LateralTheory.EtaleFoundations.EtaleKummerChernClassCochainIsCocycle := etale_first_chern_cochain_closed_of_degree_parts hd hx hr h1 h2 h3
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleFreeModuleCohomologyHomOfComponents
section
namespace LateralTheory.Fin.EtaleFreeSheafUniversalProperty
theorem etale_free_module_cohomology_hom_of_components : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := etale_free_module_cohomology_hom_of_components
end LateralTheory.Fin.EtaleFreeSheafUniversalProperty
end

-- bundled from Development.EtaleCohomology.TateTwists.PpEvDeltaPf
section
theorem LateralTheory.EtaleFoundations.pp_ev_delta_of : LateralTheory.EtaleFoundations.pp_ev_delta :=
  LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds
end

