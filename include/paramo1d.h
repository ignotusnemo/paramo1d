#ifndef PARAMO1D_H
#define PARAMO1D_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Call verification on a worker thread. The result is owned UTF-8 JSON. */
char *paramo1d_verify_json(const uint8_t *configuration, size_t length);
char *paramo1d_profile_json(void);
void paramo1d_free_json(char *value);

typedef struct Paramo1dSession Paramo1dSession;

/* Configuration: {"artifacts":"/private/app/artifacts"}.
 * All available CPUs are selected automatically. Optional threads sets a
 * smaller worker budget for applications that explicitly request it.
 * On failure, error_json receives owned JSON. Success writes NULL. */
Paramo1dSession *paramo1d_session_new_json(
    const uint8_t *configuration, size_t length, char **error_json);

/* Request: {"bundle":"/private/app/bundle"}. Calls are serialized.
 * The session retains authenticated origins and matrix span fingerprints. */
char *paramo1d_session_verify_json(
    Paramo1dSession *session, const uint8_t *configuration, size_t length);

/* Finish pending calls before releasing the session. */
void paramo1d_session_free(Paramo1dSession *session);

#ifdef __cplusplus
}
#endif

#endif
