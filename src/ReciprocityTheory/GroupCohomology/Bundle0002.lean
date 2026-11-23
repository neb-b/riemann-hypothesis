module

public import ReciprocityTheory.GroupCohomology.ContinuousContractNth

@[expose] public section

-- bundled from ReciprocityTheory.GroupCohomology.CupConnRightStatement
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

def LESStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C : Cx R) (i : Hom A B) (p : Hom B C), SES i p →
  (∃ δ, IsConn i p δ ∧ LES i p δ) ∧ ∀ δ δ', IsConn i p δ → IsConn i p δ' → δ = δ'

def ConnNatStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C A' B' C' : Cx R) (i : Hom A B) (p : Hom B C)
  (i' : Hom A' B') (p' : Hom B' C') (α : Hom A A') (β : Hom B B') (γ : Hom C C') δ δ', SES i p → SES i' p' →
  (∀ n x, β.f n (i.f n x) = i'.f n (α.f n x)) → (∀ n x, γ.f n (p.f n x) = p'.f n (β.f n x)) →
  IsConn i p δ → IsConn i' p' δ' → ∀ n x, δ' n (γ.H n x) = α.H (n + 1) (δ n x)

def TowerStatement : Prop := ∀ (R : Type u) [CommRing R] (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m))
  (L : Cx R) (π : ∀ m, Hom L (A m)), IsTowerLim A τ L π → ∀ n,
  (∀ y : ∀ m, (A m).H n, (∀ m, (τ m).H n (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).H n x = y m) ∧
  ((∀ k, n = k + 1 → ∀ m, IsArtinian R ((A m).H k)) → ∀ x : L.H n, (∀ m, (π m).H n x = 0) → x = 0)

def LowStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G),
  (∀ n, ∃ e : M.H n ≃ₗ[R] Hn M.rho n, ∀ x hx, ∃ hz : x.1 ∈ Zn M.rho n,
    e (M.coch.cls n x hx) = Submodule.Quotient.mk ⟨x.1, hz⟩) ∧
  (∃ e : M.H 0 ≃ₗ[R] H0 M.rho, ∀ x hx, (e (M.coch.cls 0 x hx) : M.V) = x.1 ![]) ∧
  (∃ e : M.H 1 ≃ₗ[R] H1 M.rho, ∀ x hx, ∃ hz : (fun g => x.1 ![g]) ∈ Z1 M.rho,
    e (M.coch.cls 1 x hx) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
  ∃ e : M.H 2 ≃ₗ[R] H2 M.rho, ∀ x hx, ∃ hz : (fun g : G × G => x.1 ![g.1, g.2]) ∈ Z2 M.rho,
    e (M.coch.cls 2 x hx) = Submodule.Quotient.mk ⟨_, hz⟩

def AdmStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A B C : TRep R G) (i : Pair A B) (p : Pair B C),
  admitted i p → SES i.hom p.hom

def GroupSectionStatement : Prop := ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (U : Subgroup G), IsClosed (U : Set G) →
  ∃ r : G → U, Continuous r ∧ r 1 = 1 ∧ ∀ (x : U) g, r (x * g) = x * r g

def InnerStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (P : Pair M M) (s : G),
  (∀ g, P.φ g = s⁻¹ * g * s) → (∀ m, P.u m = M.rho s m) → ∀ n, P.hom.H n = LinearMap.id

def InfResStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (N : Subgroup G) [N.Normal]
  (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P →
  Injective (P.hom.H 1) ∧ Exact (P.hom.H 1) ((Pair.res M N.subtype continuous_subtype_val).hom.H 1) ∧
  ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) → (∀ m, c.u m = M.rho s m) →
    ∀ n x, c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n x) =
      (Pair.res M N.subtype continuous_subtype_val).hom.H n x

def FiveTermStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
  ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P → ∀ I : Submodule R ((M.resSub N).H 1),
  (∀ x, x ∈ I ↔ ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H 1 x = x) →
  ∃ tg : I →ₗ[R] Q.H 2, (∀ x : I, tg x = 0 ↔
      x.1 ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H 1)) ∧ Exact tg (P.hom.H 2)

def CorStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (U : Subgroup G) [U.FiniteIndex], IsOpen (U : Set G) →
  ∃ cor, IsCor M U cor ∧ ∀ n x,
    cor.H n ((Pair.res M U.subtype continuous_subtype_val).hom.H n x) = U.index • x

def CupStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (b : Pairing M N P),
  (∀ p q f f' (g : Fin (p + q + 1) → G), dn P.rho (p + q) (cupFun b p q f f') g =
    cupFun b (p + 1) q (dn M.rho p f) f' (fun i => g (i.cast (by omega))) +
      (-1 : R) ^ p • cupFun b p (q + 1) f (dn N.rho q f') g) ∧
  (∃ cup, IsCup b cup) ∧ ∀ cup cup', IsCup b cup → IsCup b cup' → cup = cup'

def CupCorStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (U : Subgroup G) [U.FiniteIndex] (b : Pairing M N P)
  (bU : Pairing (M.resSub U) (N.resSub U) (P.resSub U)) cup cupU corM corP, IsOpen (U : Set G) →
  bU.β = b.β → IsCup b cup → IsCup bU cupU → IsCor M U corM → IsCor P U corP → ∀ p q x y,
    corP.H (p + q) (cupU p q x ((Pair.res N U.subtype continuous_subtype_val).hom.H q y)) =
      cup p q (corM.H p x) y

def ShapiroStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (U : Subgroup G) (M : TRep R U) (C : TRep R G)
  (ev : Pair C M), IsCoind U M C ev → (∃ r : G → U, Continuous r ∧ ∀ (x : U) g, r (x * g) = x * r g) →
  ev.hom.QuasiIso

def LimRepStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : ℕ → TRep R G) [∀ m, DiscreteTopology (A m).V]
  (τ : ∀ m, Pair (A (m + 1)) (A m)) (L : TRep R G) (π : ∀ m, Pair L (A m)),
  (∀ m, (τ m).φ = MonoidHom.id G ∧ (π m).φ = MonoidHom.id G ∧ Surjective (τ m).u ∧
    ∀ x, (τ m).u ((π (m + 1)).u x) = (π m).u x) →
  Topology.IsEmbedding (fun (x : L.V) m => (π m).u x) →
  (∀ y : ∀ m, (A m).V, (∀ m, (τ m).u (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).u x = y m) →
  IsTowerLim (fun m => (A m).coch) (fun m => (τ m).hom) L.coch fun m => (π m).hom

def FiniteLevelStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (n : ℕ) (x : M.H n),
  (∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧ ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M),
    IsInvRep M N Q P → x ∈ LinearMap.range (P.hom.H n)) ∧ (0 < n → ∃ k : ℕ, 0 < k ∧ k • x = 0)

def ModTStatement : Prop := ∀ (R : Type u) [CommRing R] (A C : Cx R) (i : Hom A A) (p : Hom A C) (t : R) δ,
  (∀ n x, i.f n x = t • x) → SES i p → IsConn i p δ → ∀ n,
  (∀ x, p.H n x = 0 ↔ ∃ y, x = t • y) ∧ Exact (p.H n) (δ n) ∧ ∀ x, x ∈ LinearMap.range (δ n) ↔ t • x = 0

def FinGenStatement : Prop := ∀ (R : Type u) [CommRing R] (t : R) [IsAdicComplete (Ideal.span {t}) R]
  (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m)),
  IsTowerLim A τ L π → (∀ n (x : L.X n), t • x = 0 → x = 0) →
  (∀ m n (x : L.X n), (π m).f n x = 0 ↔ ∃ y, x = t ^ (m + 1) • y) →
  (∀ n, IsFiniteLength R ((A 0).H n)) → ∀ n, Module.Finite R (L.H n) ∧ ∀ m, IsFiniteLength R ((A m).H n)

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.HomogExistsStatement
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def hcoch (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (n : ℕ) :
    Submodule R ((Fin (n + 1) → X) → M.V) where
  carrier := {F | Continuous F ∧ ∀ (g : G) x, F (fun i => g • x i) = M.rho g (F x)}
  zero_mem' := ⟨continuous_const, fun g x => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g x => by simp [ha.2, hb.2]⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun g x => by simp [ha.2]⟩

def hd {V X : Type u} [AddCommGroup V] (n : ℕ) (F : (Fin (n + 1) → X) → V) (x : Fin (n + 2) → X) : V :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F fun j => x (i.succAbove j)

def IsHomog (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (A : Cx R)
    (e : ∀ n, A.X n ≃ₗ[R] hcoch M X n) : Prop :=
  ∀ n a, (e (n + 1) (A.d n a)).1 = hd n (e n a).1

def HomogExistsStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X],
  ∃ A e, IsHomog M X A e

def HomogIsoStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G), ∃ e, IsHomog M G M.coch e ∧
    (∀ n f x, (e n f).1 x = M.rho (x 0) (f.1 fun i => (x i.castSucc)⁻¹ * x i.succ)) ∧
    ∀ n f g, f.1 g = (e n f).1 (Fin.partialProd g)

def PrismStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G) (X Y : Type u) [TopologicalSpace X] [MulAction G X]
  [TopologicalSpace Y] [MulAction G Y] (A B : Cx R) eA eB, IsHomog M X A eA → IsHomog M Y B eB →
  (∀ a : X → Y, Continuous a → (∀ (g : G) x, a (g • x) = g • a x) →
    ∃ φ : Hom B A, ∀ n F x, (eA n (φ.f n F)).1 x = (eB n F).1 fun i => a (x i)) ∧
  ∀ (a b : X → Y) (φ ψ : Hom B A), Continuous a → Continuous b → (∀ (g : G) x, a (g • x) = g • a x) →
    (∀ (g : G) x, b (g • x) = g • b x) → (∀ n F x, (eA n (φ.f n F)).1 x = (eB n F).1 fun i => a (x i)) →
    (∀ n F x, (eA n (ψ.f n F)).1 x = (eB n F).1 fun i => b (x i)) → ∀ n, φ.H n = ψ.H n

end

end ReciprocityTheory.Coh
end

