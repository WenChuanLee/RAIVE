
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __javax_imageio_ImageWriteParam__
#define __javax_imageio_ImageWriteParam__

#pragma interface

#include <javax/imageio/IIOParam.h>
#include <gcj/array.h>

extern "Java"
{
  namespace java
  {
    namespace awt
    {
        class Dimension;
    }
  }
  namespace javax
  {
    namespace imageio
    {
        class ImageWriteParam;
    }
  }
}

class javax::imageio::ImageWriteParam : public ::javax::imageio::IIOParam
{

public: // actually protected
  ImageWriteParam();
public:
  ImageWriteParam(::java::util::Locale *);
  virtual jfloat getBitRate(jfloat);
private:
  void checkSupportsCompression();
  void checkNotExplicitCompression();
  void checkCompressionTypesSet();
  void checkSupportsProgressiveEncoding();
  void checkSupportsTiling();
  void checkNotExplicitTiling();
  void checkTilingInitialized();
  void checkMode(jint);
public:
  virtual jboolean canOffsetTiles();
  virtual jboolean canWriteCompressed();
  virtual jboolean canWriteProgressive();
  virtual jboolean canWriteTiles();
  virtual jint getCompressionMode();
  virtual jfloat getCompressionQuality();
  virtual JArray< ::java::lang::String * > * getCompressionQualityDescriptions();
  virtual JArray< jfloat > * getCompressionQualityValues();
  virtual ::java::lang::String * getCompressionType();
  virtual JArray< ::java::lang::String * > * getCompressionTypes();
  virtual ::java::util::Locale * getLocale();
  virtual ::java::lang::String * getLocalizedCompressionTypeName();
  virtual JArray< ::java::awt::Dimension * > * getPreferredTileSizes();
  virtual jint getProgressiveMode();
  virtual jint getTileGridXOffset();
  virtual jint getTileGridYOffset();
  virtual jint getTileHeight();
  virtual jint getTileWidth();
  virtual jint getTilingMode();
  virtual jboolean isCompressionLossless();
  virtual void setCompressionMode(jint);
  virtual void setCompressionQuality(jfloat);
  virtual void setCompressionType(::java::lang::String *);
  virtual void setProgressiveMode(jint);
  virtual void setTiling(jint, jint, jint, jint);
  virtual void setTilingMode(jint);
  virtual void unsetCompression();
  virtual void unsetTiling();
  static const jint MODE_DISABLED = 0;
  static const jint MODE_DEFAULT = 1;
  static const jint MODE_EXPLICIT = 2;
  static const jint MODE_COPY_FROM_METADATA = 3;
public: // actually protected
  jboolean __attribute__((aligned(__alignof__( ::javax::imageio::IIOParam)))) canOffsetTiles__;
  jboolean canWriteCompressed__;
  jboolean canWriteProgressive__;
  jboolean canWriteTiles__;
  jint compressionMode;
  jfloat compressionQuality;
  ::java::lang::String * compressionType;
  JArray< ::java::lang::String * > * compressionTypes;
  ::java::util::Locale * locale;
  JArray< ::java::awt::Dimension * > * preferredTileSizes;
  jint progressiveMode;
  jint tileGridXOffset;
  jint tileGridYOffset;
  jint tileHeight;
  jint tileWidth;
  jint tilingMode;
  jboolean tilingSet;
public:
  static ::java::lang::Class class$;
};

#endif // __javax_imageio_ImageWriteParam__
