
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __gnu_javax_print_ipp_attribute_defaults_SidesDefault__
#define __gnu_javax_print_ipp_attribute_defaults_SidesDefault__

#pragma interface

#include <javax/print/attribute/EnumSyntax.h>
#include <gcj/array.h>

extern "Java"
{
  namespace gnu
  {
    namespace javax
    {
      namespace print
      {
        namespace ipp
        {
          namespace attribute
          {
            namespace defaults
            {
                class SidesDefault;
            }
          }
        }
      }
    }
  }
  namespace javax
  {
    namespace print
    {
      namespace attribute
      {
          class Attribute;
          class EnumSyntax;
      }
    }
  }
}

class gnu::javax::print::ipp::attribute::defaults::SidesDefault : public ::javax::print::attribute::EnumSyntax
{

public: // actually protected
  SidesDefault(jint);
public:
  ::java::lang::Class * getCategory();
  ::java::lang::String * getName();
public: // actually protected
  JArray< ::java::lang::String * > * getStringTable();
  JArray< ::javax::print::attribute::EnumSyntax * > * getEnumValueTable();
public:
  ::javax::print::attribute::Attribute * getAssociatedAttribute();
  static ::gnu::javax::print::ipp::attribute::defaults::SidesDefault * ONE_SIDED;
  static ::gnu::javax::print::ipp::attribute::defaults::SidesDefault * TWO_SIDED_LONG_EDGE;
  static ::gnu::javax::print::ipp::attribute::defaults::SidesDefault * TWO_SIDED_SHORT_EDGE;
  static ::gnu::javax::print::ipp::attribute::defaults::SidesDefault * DUPLEX;
  static ::gnu::javax::print::ipp::attribute::defaults::SidesDefault * TUMBLE;
private:
  static JArray< ::java::lang::String * > * stringTable;
  static JArray< ::gnu::javax::print::ipp::attribute::defaults::SidesDefault * > * enumValueTable;
public:
  static ::java::lang::Class class$;
};

#endif // __gnu_javax_print_ipp_attribute_defaults_SidesDefault__
