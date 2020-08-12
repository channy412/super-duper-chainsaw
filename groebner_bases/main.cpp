#include <iostream>
#include <vector>
#include <gmp.h>
#include <gmpxx.h>
#include <cassert>
#include <list>
#include <iterator>

class Monomial {
public:
    mpq_class coefficient;
    std::vector<unsigned int> degrees;

    Monomial(mpq_class coefficient, std::vector<unsigned int> degrees) :
            coefficient(coefficient), degrees(degrees) {};
    // When we pass an array to a function, a pointer is actually passed.
    // When a vector is passed to a function, a copy of the vector is created. so it is deep-copy in this case

    Monomial(mpq_class coefficient, unsigned int arr[], int n) {
        this->coefficient = coefficient;
        for (int i = 0; i < n; i++) {
            this->degrees.push_back(arr[i]);
        }
    }


    Monomial copy() {
        Monomial m(coefficient, degrees);
        return m;
    }

    Monomial copy_minus() {
        Monomial m(-coefficient, degrees);
        return m;
    }


    Monomial operator+(Monomial const m) {
        //  assert( this.degrees == m.degrees )
        for (int i = 0; i < this->degrees.size(); i++) {
            if (this->degrees[i] != m.degrees[i]) {
                printf("monomial addition error \n");
                static_assert(-1);
            }
        }

        return Monomial(this->coefficient + m.coefficient, this->degrees);
    }

    Monomial operator-(Monomial const m) {
        //  assert( this.degrees == m.degrees )
        for (int i = 0; i < this->degrees.size(); i++) {
            if (this->degrees[i] != m.degrees[i]) {
                printf("monomial subtraction error \n");
                static_assert(-1);
            }
        }

        return Monomial(this->coefficient - m.coefficient, this->degrees);
    }

    Monomial operator*(Monomial const m) {
        unsigned int *p;
        std::vector<unsigned int> result_degree;
        p = result_degree.get_allocator().allocate(this->degrees.size()); // reserve space in advance
        for (int i = 0; i < this->degrees.size(); i++) {
            result_degree.push_back(this->degrees[i] + m.degrees[i]);
        }
        return Monomial(this->coefficient * m.coefficient, result_degree);
    }

    Monomial operator/(Monomial const m) {
        unsigned int *p;
        std::vector<unsigned int> result_degree;
        p = result_degree.get_allocator().allocate(this->degrees.size()); // reserve space in advance
        for (int i = 0; i < this->degrees.size(); i++) {
            result_degree.push_back(this->degrees[i] - m.degrees[i]);
            if (this->degrees[i] < m.degrees[i]) {
                printf("monomial division error \n");
                assert(-1);
            }
        }
        return Monomial(this->coefficient / m.coefficient, result_degree);
    }
};

std::ostream &operator<<(std::ostream &out, Monomial m) {
    out << m.coefficient;
    for (int i = 0; i < m.degrees.size(); ++i) {
        if (m.degrees[i] == 0) continue;
        out << " " << "X_" << i << "^" << m.degrees[i];
    }
    return out;
}

// now make linked list which has a monomial as its node's item
// should make it efficient for real usage
class Polynomial {
public:
    std::list<Monomial> list;

    int (*order)(Monomial m1, Monomial m2);

    Polynomial(int (*order)(Monomial, Monomial)) {
        this->order = order;
    }


    void setLeadingCoeffOne() {
        mpq_class coeff = 1 / list.front().coefficient;
        if (coeff == 0) {
            std::cout << "setLeadingCoeffOne error: leading term's coeff is zero, polynomial: ";
        }
        for (auto &item : list) {
            item.coefficient = item.coefficient * coeff;
        }
    }


    void insert_monomial(Monomial m) {
        if (m.coefficient == 0) return;

        if (list.empty()) {
            list.push_back(m);
            return;
        }

        // find appropriate location
        std::list<Monomial>::iterator iterator;


        // shall not dereference list.end() iterator
        for (iterator = list.begin(); iterator != list.end(); ++iterator) {
            if (order(m, *iterator) > -1) {
                break;
            }
        }


        // erase (delete from the list) if the coefficient becomes zero
        if (iterator == list.end()) {
            list.push_back(m);

        } else if (order(m, *iterator) == 0) {
            *iterator = *iterator + m;
            Monomial tmp = *iterator;
            if (tmp.coefficient == 0) {
                list.erase(iterator);
            }
        } else {
            list.insert(iterator, m);
        }
    }

    void print() {
        if (this->isZero()) {
            std::cout << "Zero Polynomial" << std::endl;
        }

        std::list<Monomial>::iterator iterator;

        for (iterator = list.begin(); iterator != list.end(); ++iterator) {
            std::cout << *iterator;
            if (std::next(iterator) != list.end()) std::cout << "  +  ";
        }
        std::cout << std::endl;

    }

    bool isZero() {
        return list.empty();
    }

    int size() {
        return list.size();
    }


    int comparator(const void *ptr1, const void *ptr2) {
        Monomial m1 = *(Monomial *) ptr1;
        Monomial m2 = *(Monomial *) ptr2;

        return order(m1, m2);
    }

    Polynomial copy() {
        Polynomial p(order);
        std::list<Monomial>::iterator iterator;
        for (iterator = list.begin(); iterator != list.end(); ++iterator) {
            Monomial a = *iterator;
            p.insert_monomial(a.copy());
        }
        return p;
    }

    Polynomial copy_minus() {
        Polynomial p(order);
        std::list<Monomial>::iterator iterator;
        for (iterator = list.begin(); iterator != list.end(); ++iterator) {
            Monomial a = *iterator;
            p.insert_monomial(a.copy_minus());
        }
        return p;
    }

    Polynomial operator+(Polynomial p) {
        assert(order == p.order);
        Polynomial p1 = this->copy();
        Polynomial p2 = p.copy();
        std::list<Monomial>::iterator iterator;
        for (iterator = p2.list.begin(); iterator != p2.list.end(); ++iterator) {
            Monomial a = *iterator;
            p1.insert_monomial(a.copy());
        }
        return p1;
    }

    Polynomial operator-(Polynomial p) {
        assert(order == p.order);
        Polynomial p1 = this->copy();
        Polynomial p2 = p.copy_minus();

        std::list<Monomial>::iterator iterator;
        for (iterator = p2.list.begin(); iterator != p2.list.end(); ++iterator) {
            Monomial a = *iterator;
            p1.insert_monomial(a.copy());
        }
        return p1;
    }

    Polynomial operator*(Polynomial p) {
        assert(order == p.order);
        Polynomial p_mul = Polynomial(order);
        Polynomial p1 = this->copy();
        Polynomial p2 = p.copy();
        std::list<Monomial>::iterator iterator1;
        std::list<Monomial>::iterator iterator2;
        for (iterator1 = p1.list.begin(); iterator1 != p1.list.end(); ++iterator1) {
            for (iterator2 = p2.list.begin(); iterator2 != p2.list.end(); ++iterator2) {
                Monomial a = (*iterator1) * (*iterator2);
                p_mul.insert_monomial(a);
            }
        }
        return p_mul;
    }

};

int lexicographic_order(Monomial m1, Monomial m2) {
    // 1 if order(m1)>order(m2) ,  0 if it is same,  else  -1

    for (int i = 0; i < m1.degrees.size(); i++) {
        if (m1.degrees[i] < m2.degrees[i]) return -1;
        else if (m1.degrees[i] > m2.degrees[i]) return 1;
    }
    return 0;
}

int graded_lexicographic(Monomial m1, Monomial m2) {
    // 1 if order(m1)>order(m2) ,  0 if it is same,  else  -1

    int total_deg1 = 0;
    int total_deg2 = 0;

    for (int i = 0; i < m1.degrees.size(); i++) {
        total_deg1 += m1.degrees[i];
        total_deg2 += m2.degrees[i];
    }

    if (total_deg1 > total_deg2) return 1;
    else if (total_deg1 < total_deg2) return -1;
    else {
        for (int i = 0; i < m1.degrees.size(); i++) {
            if (m1.degrees[i] < m2.degrees[i]) return -1;
            else if (m1.degrees[i] > m2.degrees[i]) return 1;
        }
    }
    return 0;
}

int dividable(Polynomial p, std::vector<Polynomial> &vector){
    // used in div_rem
    //  returns i if lt(p) can be divided by lt(p_i)
    //  returns -1 if not possible


    // zero poly, nothing to divide
    if (p.size() == 0) return -1;

    for (int i = 0; i < vector.size(); i++) {
        // if zero poly, continue
        if (vector[i].list.empty()) continue;

        // get degree of leading term
        std::vector<unsigned int> p_degrees = p.list.front().degrees;
        std::vector<unsigned int> p_i_degrees = vector[i].list.front().degrees;


        int z = 0;
        for (int j = 0; j < p_degrees.size(); j++) {
            if (p_degrees[j] < p_i_degrees[j]) {
                // not dividable
                z = 1;
                break;
            }
        }
        if (z == 0) return i;
    }
    return -1;
}

Polynomial S_polynomial(Polynomial g, Polynomial h) {
    if (g.isZero() || h.isZero()) {
        std::cout << "input of S_poly is zero poly" << std::endl;
        static_assert(-1);
    }

    // get leading terms
    Monomial alpha = g.list.front();
    Monomial beta = h.list.front();

    std::vector<unsigned int> degree_a = alpha.degrees;
    std::vector<unsigned int> degree_b = beta.degrees;


    unsigned int *p;
    std::vector<unsigned int> max;
    p = max.get_allocator().allocate(degree_a.size()); // reserve space in advance

    for (int i = 0; i < degree_a.size(); i++) {
        max.push_back(degree_a[i] > degree_b[i] ? degree_a[i] : degree_b[i]);
    }

    mpq_class coeff(1, 1);
    Monomial gamma = Monomial(coeff, max);


    Polynomial p1(g.order);
    Polynomial p2(g.order);

    // wrapper poly for monomials
    p1.insert_monomial(gamma / alpha);
    p2.insert_monomial(gamma / beta);

    return g * p1 - h * p2;
}

Polynomial div_rem(Polynomial f, std::vector<Polynomial> &vector) {
    if (vector.empty()) { return f; }


    Polynomial p = f.copy();


    // keep subtraction and return p if any poly cannot 'divide' p
    int condition = dividable(p, vector);
    while (condition != -1) {
        Polynomial dividor = vector[condition];

        //  division between leading terms
        Monomial q_i = p.list.front() / dividor.list.front();

        // wrapper Polynomial
        Polynomial q_i_wrapper = Polynomial(f.order);
        q_i_wrapper.insert_monomial(q_i);


        // main part of division and remainder
        p = (p - q_i_wrapper * dividor).copy();

        condition = dividable(p, vector);
    }
    return p;
}

int dividable_without_i(std::vector<Polynomial> &vector, int l) {
    // used in makeGBMinimal
    //  returns j if lt(p_i) can be divided by lt(p_j) (i != j)
    //  returns -1 if not possible

    Polynomial p = vector[l];

    // zero poly, nothing to divide
    if (p.size() == 0) return -1;

    for (int i = 0; i < vector.size(); i++) {
        // get degree of leading term
        // if zero poly, continue
        if (i == l) continue; //   { G  - { p_i }
        if (vector[i].list.empty()) continue;

        std::vector<unsigned int> p_degrees = p.list.front().degrees;
        std::vector<unsigned int> p_i_degrees = vector[i].list.front().degrees;


        int z = 0;
        for (int j = 0; j < p_degrees.size(); j++) {
            if (p_degrees[j] < p_i_degrees[j]) {
                // not dividable
                z = 1;
                break;
            }
        }
        if (z == 0) return i;
    }
    return -1;
}

void makeGBMinimal(std::vector<Polynomial> &vector) {

    // make coefficients of leading term  to 1
    for (int i = 0; i < vector.size(); ++i) {
        vector[i].setLeadingCoeffOne();
    }

    std::vector<Polynomial>::iterator iterator;
    for (iterator = vector.begin(); iterator != vector.end();) {
        if (dividable_without_i(vector, iterator - vector.begin()) != -1) {
            iterator = vector.erase(iterator);
        } else {
            iterator++;
        }
    }
}

int divisible_without_i(std::vector<Monomial> &lt_vector, Monomial monomial, int l) {
    // used in makeGBReduced
    // returns j if  monominal is divisible by lt(p_j)   (l != j)
    //  returns -1 if not possible

    for (int i = 0; i < lt_vector.size(); i++) {
        if (i == l) continue; //   { lt(G)  - lt(p_i)

        std::vector<unsigned int> p_degrees = monomial.degrees;
        std::vector<unsigned int> p_i_degrees = lt_vector[i].degrees;

        int z = 0;
        for (int j = 0; j < p_degrees.size(); j++) {

            if (p_degrees[j] < p_i_degrees[j]) {
                // not dividable
                z = 1;
                break;
            }
        }
        if (z == 0) return i;
    }
    return -1;
}

void makeGBReduced(std::vector<Polynomial> &vector) {
    // set of leading terms
    std::vector<Monomial> lt_vector;
    for (Polynomial p: vector) {
        lt_vector.push_back(p.list.front());
    }

    for (int i = 0; i < vector.size(); ++i) {
        std::list<Monomial> list = vector[i].list;
        std::list<Monomial>::iterator iterator;
        for (iterator = list.begin(); iterator != list.end(); iterator) {
            if (divisible_without_i(lt_vector, *iterator, i) != -1) iterator = list.erase(iterator);
            else iterator++;
        }
    }
}

void autoReduction(std::vector<Polynomial> &vector) {
    makeGBMinimal(vector);
    makeGBReduced(vector);
}

std::pair<int, int> buchbergerCriterion(std::vector<Polynomial> &vector) {
    // if it is GB, return (-1,-1)
    // else, i.e.  if  S_poly of (P_i, P_j) is non zero,  return (i,j)
    std::pair<int, int> pair;

    for (int i = 0; i < vector.size(); i++) {
        for (int j = 0; j < vector.size(); j++) {
            Polynomial p = div_rem(S_polynomial(vector[i], vector[j]), vector);
            if (!p.isZero()) {
                pair.first = i;
                pair.second = j;
                return pair;
            }
        }
    }
    pair.first = -1;
    pair.second = -1;
    return pair;
}

void ComputeGB(std::vector<Polynomial> &vector) {
    std::pair<int, int> pair;
    while (true) {
        pair = buchbergerCriterion(vector);
        if (pair.first == -1) return;
        Polynomial p = div_rem(S_polynomial(vector[pair.first], vector[pair.second]), vector);
        vector.push_back(p);
    }
}

int main() {



    // 1.1 simple example

    mpq_class one(1, 1);
    unsigned int constant[] = {0, 0, 0};
    unsigned int x2[] = {2, 0, 0};
    unsigned int y2[] = {0, 2, 0};
    unsigned int z2[] = {0, 0, 2};
    unsigned int x3[] = {3, 0, 0};

    Monomial x_sq(one, x2, 3);
    Monomial y_sq(one, y2, 3);
    Monomial z_sq(one, z2, 3);
    Monomial one_m(-one, constant, 3);

    Monomial x_cubed(one, x3, 3);
    Monomial y_sq_m(-one, y2, 3);
    Monomial z_sq_m(-one, z2, 3);

    Polynomial P1(lexicographic_order);
    Polynomial P2(lexicographic_order);

    P1.insert_monomial(x_sq);
    P1.insert_monomial(y_sq);
    P1.insert_monomial(z_sq);
    P1.insert_monomial(one_m);

    P2.insert_monomial(x_cubed);
    P2.insert_monomial(x_sq);
    P2.insert_monomial(y_sq_m);
    P2.insert_monomial(z_sq_m);


    std::cout << "Input of 1.1: " << std::endl;
    P1.print();
    P2.print();

    std::vector<Polynomial> vector;
    vector.push_back(P1);
    vector.push_back(P2);


    ComputeGB(vector);
    autoReduction(vector);


    std::cout << "Reduced ComputeGB of 1.1: " << std::endl;
    for (int i = 0; i < vector.size(); ++i) {
        vector[i].print();
    }
    std::cout << std::endl;




    // 1.1.1 twisted cubic
    // t, x, y, z   order
    unsigned int t[] = {1, 0, 0, 0};
    unsigned int t2[] = {2, 0, 0, 0};
    unsigned int t3[] = {3, 0, 0, 0};
    unsigned int x[] = {0, 1, 0, 0};
    unsigned int y[] = {0, 0, 1, 0};
    unsigned int z[] = {0, 0, 0, 1};

    Monomial t_1(-one, t, 4);
    Monomial t_2(-one, t2, 4);
    Monomial t_3(-one, t3, 4);
    Monomial x_111(one, x, 4);
    Monomial y_111(one, y, 4);
    Monomial z_111(one, z, 4);

    Polynomial p11(lexicographic_order);
    Polynomial p12(lexicographic_order);
    Polynomial p13(lexicographic_order);

    p11.insert_monomial(x_111);
    p11.insert_monomial(t_1);
    p12.insert_monomial(t_2);
    p12.insert_monomial(y_111);
    p13.insert_monomial(t_3);
    p13.insert_monomial(z_111);


    Polynomial p21(graded_lexicographic);
    Polynomial p22(graded_lexicographic);
    Polynomial p23(graded_lexicographic);

    p21.insert_monomial(x_111);
    p21.insert_monomial(t_1);
    p22.insert_monomial(t_2);
    p22.insert_monomial(y_111);
    p23.insert_monomial(t_3);
    p23.insert_monomial(z_111);

    std::vector<Polynomial> vector2;
    vector2.push_back(p11);
    vector2.push_back(p12);
    vector2.push_back(p13);

    ComputeGB(vector2);
    autoReduction(vector2);


    std::cout << "Input of 1.1.1: " << std::endl;
    p11.print();
    p12.print();
    p13.print();


    std::cout << "Reduced ComputeGB of 1.1.1 , lexicographic, t>x>y>z: " << std::endl;
    for (int i = 0; i < vector2.size(); ++i) {
        vector2[i].print();
    }
    std::cout << std::endl;


    std::vector<Polynomial> vector3;
    vector3.push_back(p21);
    vector3.push_back(p22);
    vector3.push_back(p23);

    ComputeGB(vector3);
    autoReduction(vector3);


    std::cout << "Input of 1.1.1: " << std::endl;
    p21.print();
    p22.print();
    p23.print();

    std::cout << "Reduced ComputeGB of 1.1.1, graded lexi, t>x>y>z : " << std::endl;
    for (int i = 0; i < vector3.size(); ++i) {
        vector3[i].print();
    }
    std::cout << std::endl;

    return 0;
}
