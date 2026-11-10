#include <jni.h>
#include <stdlib.h>
#include <string.h>
extern char *Paramo1dTunnelCall(char *);
extern void Paramo1dTunnelFree(char *);
JNIEXPORT jstring JNICALL Java_org_parano1d_courier_NativeTunnel_call(JNIEnv *env, jclass cls, jstring request) {
    if (!request || (*env)->GetStringLength(env,request)>2097152) return (*env)->NewStringUTF(env,"{\"ok\":false,\"error\":\"Tunnel request exceeds limit\"}");
    jclass string=(*env)->FindClass(env,"java/lang/String");
    jmethodID encode=(*env)->GetMethodID(env,string,"getBytes","(Ljava/lang/String;)[B");
    jstring utf8=(*env)->NewStringUTF(env,"UTF-8");
    jbyteArray bytes=(jbyteArray)(*env)->CallObjectMethod(env,request,encode,utf8);
    if ((*env)->ExceptionCheck(env) || !bytes) return NULL;
    jsize length=(*env)->GetArrayLength(env,bytes);
    if (length>2097152) return (*env)->NewStringUTF(env,"{\"ok\":false,\"error\":\"Tunnel request exceeds limit\"}");
    char *input=calloc((size_t)length+1,1);if (!input) return NULL;
    (*env)->GetByteArrayRegion(env,bytes,0,length,(jbyte *)input);
    char *output=Paramo1dTunnelCall(input);memset(input,0,(size_t)length);free(input);
    jbyteArray resultBytes=(*env)->NewByteArray(env,(jsize)strlen(output));
    if (!resultBytes){Paramo1dTunnelFree(output);return NULL;}
    (*env)->SetByteArrayRegion(env,resultBytes,0,(jsize)strlen(output),(const jbyte *)output);Paramo1dTunnelFree(output);
    jmethodID decode=(*env)->GetMethodID(env,string,"<init>","([BLjava/lang/String;)V");
    return (jstring)(*env)->NewObject(env,string,decode,resultBytes,utf8);
}
