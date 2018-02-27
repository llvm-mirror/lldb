add_lldb_library(lldbPluginDLanguage PLUGIN
  DLanguage.cpp
  
  LINK_LIBS
    lldbCore
    lldbTarget
)
