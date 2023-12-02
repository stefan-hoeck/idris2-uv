#include <stdio.h>
#include <uv.h>

void fileFlag(char *name, int flag);

void mode(char *name, int flag);

int main(void) {
  printf("\npublic export\ndirentCode : DirentType -> Bits32\n");
  printf("direntCode DirentUnknown = %d\n", UV_DIRENT_UNKNOWN);
  printf("direntCode DirentFile    = %d\n", UV_DIRENT_FILE);
  printf("direntCode DirentDir     = %d\n", UV_DIRENT_DIR);
  printf("direntCode DirentLink    = %d\n", UV_DIRENT_LINK);
  printf("direntCode DirentFifo    = %d\n", UV_DIRENT_FIFO);
  printf("direntCode DirentSocket  = %d\n", UV_DIRENT_SOCKET);
  printf("direntCode DirentChar    = %d\n", UV_DIRENT_CHAR);
  printf("direntCode DirentBlock   = %d\n", UV_DIRENT_BLOCK);

  printf("\npublic export\ndirentFromCode : Bits32 -> DirentType\n");
  printf("direntFromCode %d = DirentFile\n",   UV_DIRENT_FILE);
  printf("direntFromCode %d = DirentDir\n",    UV_DIRENT_DIR);
  printf("direntFromCode %d = DirentLink\n",   UV_DIRENT_LINK);
  printf("direntFromCode %d = DirentFifo\n",   UV_DIRENT_FIFO);
  printf("direntFromCode %d = DirentSocket\n", UV_DIRENT_SOCKET);
  printf("direntFromCode %d = DirentChar\n",   UV_DIRENT_CHAR);
  printf("direntFromCode %d = DirentBlock\n",  UV_DIRENT_BLOCK);
  printf("direntFromCode _ = DirentUnknown\n");

  fileFlag("APPEND", UV_FS_O_APPEND);
  fileFlag("CREAT", UV_FS_O_CREAT);
  fileFlag("DIRECT", UV_FS_O_DIRECT);
  fileFlag("DIRECTORY", UV_FS_O_DIRECTORY);
  fileFlag("NOATIME", UV_FS_O_NOATIME);
  fileFlag("NOCTTY", UV_FS_O_NOCTTY);
  fileFlag("NOFOLLOW", UV_FS_O_NOFOLLOW);
  fileFlag("NONBLOCK", UV_FS_O_NONBLOCK);
  fileFlag("RANDOM", UV_FS_O_RANDOM);
  fileFlag("RDONLY", UV_FS_O_RDONLY);
  fileFlag("RDWR", UV_FS_O_RDWR);
  fileFlag("SEQUENTIAL", UV_FS_O_SEQUENTIAL);
  fileFlag("SHORT_LIVED", UV_FS_O_SHORT_LIVED);
  fileFlag("SYMLINK", UV_FS_O_SYMLINK);
  fileFlag("SYNC", UV_FS_O_SYNC);
  fileFlag("TEMPORARY", UV_FS_O_TEMPORARY);
  fileFlag("TRUNC", UV_FS_O_TRUNC);
  fileFlag("WRONLY", UV_FS_O_WRONLY);

  mode("RWXU", S_IRWXU);
  mode("RUSR", S_IRUSR);
  mode("WUSR", S_IWUSR);
  mode("XUSR", S_IXUSR);
  mode("RWXG", S_IRWXG);
  mode("RGRP", S_IRGRP);
  mode("WGRP", S_IWGRP);
  mode("XGRP", S_IXGRP);
  mode("RWXO", S_IRWXO);
  mode("ROTH", S_IROTH);
  mode("WOTH", S_IWOTH);
  mode("XOTH", S_IXOTH);
}

void fileFlag(char *name, int flag){
    printf("\nexport %%inline\n");
    printf("%s : Flags\n", name);
    printf("%s = %d\n", name, flag);
}

void mode(char *name, int flag){
    printf("\nexport %%inline\n");
    printf("%s : File.Mode\n", name);
    printf("%s = %d\n", name, flag);
}
