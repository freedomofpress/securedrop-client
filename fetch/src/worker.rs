use std::collections::HashSet;
use std::sync::{Arc, RwLock};

use anyhow::Result;
use tokio::task;

use crate::db::{DB, Status};

pub(crate) type SharedSet<T> = Arc<RwLock<HashSet<T>>>;

pub(crate) struct Worker {
    db: DB,
    active_fetches: SharedSet<String>,
}

impl Worker {
    pub(crate) fn spawn(
        db_path: String,
        active_fetches: SharedSet<String>,
    ) -> Result<task::JoinHandle<()>> {
        let db = DB::new(db_path)?;
        let worker = Self { db, active_fetches };
        let join_handle = task::spawn(async move { worker.fetch_downloads() });
        return Ok(join_handle);
    }

    fn fetch_downloads(&self) {
        loop {
            if let Err(e) = self.fetch_download() {
                eprintln!("error fetching download: {:?}", e);
                // TODO(vicki): backoff + retry
            }
        }
    }

    fn fetch_download(&self) -> Result<()> {
        if let Some(item_uuid) = self.get_next_download()? {
            match self.fetch_download_tick() {
                Status::InProgress => {
                    // TODO(vicki): get progress
                    self.db.update_item_progress(item_uuid, 0)?
                }
                status => {
                    self.db.update_item_status(item_uuid.clone(), status)?;
                    if status == Status::Complete {
                        self.active_fetches.write().unwrap().remove(&item_uuid);
                    }
                }
            }
        }
        Ok(())
    }

    fn fetch_download_tick(&self) -> Status {
        todo!()
    }

    fn get_next_download(&self) -> Result<Option<String>> {
        // acquire write lock
        let mut write_lock = self.active_fetches.write().unwrap();
        let download_items: HashSet<String> =
            self.db.get_items_to_fetch()?.into_iter().collect();
        let mut eligible_download_items =
            download_items.difference(&write_lock);
        if let Some(item) = eligible_download_items.next().cloned() {
            write_lock.insert(item.clone());
            return Ok(Some(item));
        }
        Ok(None)
    }
}
