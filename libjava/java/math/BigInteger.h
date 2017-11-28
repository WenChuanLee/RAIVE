
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __java_math_BigInteger__
#define __java_math_BigInteger__

#pragma interface

#include <java/lang/Number.h>
#include <gcj/array.h>

extern "Java"
{
  namespace gnu
  {
    namespace java
    {
      namespace lang
      {
          class CPStringBuilder;
      }
      namespace math
      {
          class GMP;
      }
    }
  }
  namespace java
  {
    namespace math
    {
        class BigInteger;
    }
  }
}

class java::math::BigInteger : public ::java::lang::Number
{

  BigInteger();
  BigInteger(jint);
public:
  BigInteger(::java::lang::String *, jint);
  BigInteger(::java::lang::String *);
  BigInteger(JArray< jbyte > *);
  BigInteger(jint, JArray< jbyte > *);
  BigInteger(jint, ::java::util::Random *);
private:
  void init(jint, ::java::util::Random *);
public:
  BigInteger(jint, jint, ::java::util::Random *);
  static ::java::math::BigInteger * probablePrime(jint, ::java::util::Random *);
  static ::java::math::BigInteger * valueOf(jlong);
private:
  static jboolean initializeLibrary();
  static ::java::math::BigInteger * make(JArray< jint > *, jint);
  static JArray< jint > * byteArrayToIntArray(JArray< jbyte > *, jint);
  static ::java::math::BigInteger * alloc(jint);
  void realloc(jint);
  jboolean isNegative();
public:
  virtual jint signum();
private:
  static jint compareTo(::java::math::BigInteger *, ::java::math::BigInteger *);
public:
  virtual jint BigInteger$compareTo(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * min(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * max(::java::math::BigInteger *);
private:
  jboolean isZero();
  jboolean isOne();
  static jint wordsNeeded(JArray< jint > *, jint);
  ::java::math::BigInteger * canonicalize();
  static ::java::math::BigInteger * add(jint, jint);
  static ::java::math::BigInteger * add(::java::math::BigInteger *, jint);
  void setAdd(::java::math::BigInteger *, jint);
  void setAdd(jint);
  void set(jlong);
  void set(JArray< jint > *, jint);
  void set(::java::math::BigInteger *);
  static ::java::math::BigInteger * add(::java::math::BigInteger *, ::java::math::BigInteger *, jint);
public:
  virtual ::java::math::BigInteger * add(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * subtract(::java::math::BigInteger *);
private:
  static ::java::math::BigInteger * times(::java::math::BigInteger *, jint);
  static ::java::math::BigInteger * times(::java::math::BigInteger *, ::java::math::BigInteger *);
public:
  virtual ::java::math::BigInteger * multiply(::java::math::BigInteger *);
private:
  static void divide(jlong, jlong, ::java::math::BigInteger *, ::java::math::BigInteger *, jint);
  static void divide(::java::math::BigInteger *, ::java::math::BigInteger *, ::java::math::BigInteger *, ::java::math::BigInteger *, jint);
public:
  virtual ::java::math::BigInteger * divide(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * remainder(::java::math::BigInteger *);
  virtual JArray< ::java::math::BigInteger * > * divideAndRemainder(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * mod(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * pow(jint);
private:
  static JArray< jint > * euclidInv(jint, jint, jint);
  static void euclidInv(::java::math::BigInteger *, ::java::math::BigInteger *, ::java::math::BigInteger *, JArray< ::java::math::BigInteger * > *);
public:
  virtual ::java::math::BigInteger * modInverse(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * modPow(::java::math::BigInteger *, ::java::math::BigInteger *);
private:
  static jint gcd(jint, jint);
public:
  virtual ::java::math::BigInteger * gcd(::java::math::BigInteger *);
  virtual jboolean isProbablePrime(jint);
private:
  void setInvert();
  void setShiftLeft(::java::math::BigInteger *, jint);
  void setShiftRight(::java::math::BigInteger *, jint);
  void setShift(::java::math::BigInteger *, jint);
  static ::java::math::BigInteger * shift(::java::math::BigInteger *, jint);
public:
  virtual ::java::math::BigInteger * shiftLeft(jint);
  virtual ::java::math::BigInteger * shiftRight(jint);
private:
  void format(jint, ::gnu::java::lang::CPStringBuilder *);
public:
  virtual ::java::lang::String * toString();
  virtual ::java::lang::String * toString(jint);
  virtual jint intValue();
  virtual jlong longValue();
  virtual jint hashCode();
private:
  static jboolean equals(::java::math::BigInteger *, ::java::math::BigInteger *);
public:
  virtual jboolean equals(::java::lang::Object *);
private:
  static ::java::math::BigInteger * valueOf(JArray< jbyte > *, jint, jboolean, jint);
public:
  virtual jdouble doubleValue();
  virtual jfloat floatValue();
private:
  jboolean checkBits(jint);
  jdouble roundToDouble(jint, jboolean, jboolean);
  void getAbsolute(JArray< jint > *);
  static jboolean negate(JArray< jint > *, JArray< jint > *, jint);
  void setNegative(::java::math::BigInteger *);
  void setNegative();
  static ::java::math::BigInteger * abs(::java::math::BigInteger *);
public:
  virtual ::java::math::BigInteger * abs();
private:
  static ::java::math::BigInteger * neg(::java::math::BigInteger *);
public:
  virtual ::java::math::BigInteger * negate();
  virtual jint bitLength();
  virtual JArray< jbyte > * toByteArray();
private:
  static jint swappedOp(jint);
  static ::java::math::BigInteger * bitOp(jint, ::java::math::BigInteger *, ::java::math::BigInteger *);
  static void setBitOp(::java::math::BigInteger *, jint, ::java::math::BigInteger *, ::java::math::BigInteger *);
  static ::java::math::BigInteger * and$(::java::math::BigInteger *, jint);
public:
  virtual ::java::math::BigInteger * and$(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * or$(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * xor$(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * not$();
  virtual ::java::math::BigInteger * andNot(::java::math::BigInteger *);
  virtual ::java::math::BigInteger * clearBit(jint);
  virtual ::java::math::BigInteger * setBit(jint);
  virtual jboolean testBit(jint);
  virtual ::java::math::BigInteger * flipBit(jint);
  virtual jint getLowestSetBit();
private:
  static jint bitCount(jint);
  static jint bitCount(JArray< jint > *, jint);
public:
  virtual jint bitCount();
private:
  void readObject(::java::io::ObjectInputStream *);
  void writeObject(::java::io::ObjectOutputStream *);
public:
  virtual jint compareTo(::java::lang::Object *);
private:
  static ::java::util::logging::Logger * log;
  jint __attribute__((aligned(__alignof__( ::java::lang::Number)))) ival;
  JArray< jint > * words;
  jint bitCount__;
  jint bitLength__;
  jint lowestSetBit;
  JArray< jbyte > * magnitude;
  jint signum__;
  static const jlong serialVersionUID = -8287574255936472291LL;
  static const jint minFixNum = -100;
  static const jint maxFixNum = 1024;
  static const jint numFixNum = 1125;
  static JArray< ::java::math::BigInteger * > * smallFixNums;
  ::gnu::java::math::GMP * mpz;
  static jboolean USING_NATIVE;
public:
  static ::java::math::BigInteger * ZERO;
  static ::java::math::BigInteger * ONE;
  static ::java::math::BigInteger * TEN;
private:
  static const jint FLOOR = 1;
  static const jint CEILING = 2;
  static const jint TRUNCATE = 3;
  static const jint ROUND = 4;
  static JArray< jint > * primes;
  static JArray< jint > * k;
  static JArray< jint > * t;
  static JArray< jbyte > * bit4_count;
public:
  static ::java::lang::Class class$;
};

#endif // __java_math_BigInteger__
